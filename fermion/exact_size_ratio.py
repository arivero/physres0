#!/usr/bin/env python3
"""
Exact size ratio verification using Numerov solver with node counting.

Key insight: the Numerov method produces many spurious sign changes at
energies far from the true eigenvalue (due to numerical overflow of
exponentially growing solutions). We identify the true GROUND STATE
by counting nodes of the wavefunction.

The ground state has 0 nodes (excluding r=0 and r→∞).
"""
import sys
import numpy as np
from scipy.optimize import brentq

_trapz = getattr(np, 'trapezoid', np.trapz)

# ======================================================================
# Grid and potentials
# ======================================================================

h = 0.02
r_max = 30.0
r = np.arange(h, r_max, h)
N = len(r)
print(f"Grid: {N} points, h={h}, r_max={r_max}", flush=True)

V_yuk_unit = -np.exp(-r) / (4 * np.pi * r)

# Fermion loop (vectorized)
print("Computing fermion potential...", flush=True)
s_grid = np.linspace(4.01, 500.0, 600)
ds = s_grid[1] - s_grid[0]
beta2 = 1 - 4.0/s_grid
rho_v = np.where(beta2 > 0, s_grid * beta2**1.5 / (8*np.pi), 0.0)
sqrt_s = np.sqrt(s_grid)

V_fer_unit = np.zeros(N)
for start in range(0, N, 300):
    end = min(start + 300, N)
    exp_mat = np.exp(-sqrt_s[None, :] * r[start:end, None])
    V_fer_unit[start:end] = -np.dot(exp_mat, rho_v) * ds / (2*np.pi) / (4*np.pi*r[start:end])
print("  done.", flush=True)

# ======================================================================
# Numerov solver with node counting
# ======================================================================

def numerov_wf(V_arr, E, L=0):
    """Numerov integration, returns (u, n_nodes)."""
    f = 2.0 * (V_arr - E) + L*(L+1) / r**2
    u = np.zeros(N)
    u[0] = r[0]**(L+1)
    u[1] = r[1]**(L+1)
    h2 = h * h
    n_nodes = 0
    u_max = abs(u[1])

    for i in range(1, N - 1):
        u[i+1] = (2*u[i]*(1 - 5*h2*f[i]/12) - u[i-1]*(1 + h2*f[i-1]/12)) / (1 + h2*f[i+1]/12)

        # Count nodes (sign changes, excluding near-zero values)
        if abs(u[i]) > 1e-10 * u_max and abs(u[i+1]) > 1e-10 * u_max:
            if u[i] * u[i+1] < 0:
                n_nodes += 1

        u_max = max(u_max, abs(u[i+1]))

        if abs(u[i+1]) > 1e15:
            u[i+1:] = np.sign(u[i+1]) * 1e15
            break
    return u, n_nodes

def find_ground_state(V_arr, E_lo, E_hi, L=0, n_scan=300):
    """Find ground state (0 nodes) by scanning energy."""
    # Strategy: scan from E_hi (near threshold) downward.
    # The ground state is the eigenvalue where u(r_max) changes sign
    # AND the wavefunction has 0 nodes.
    Es = np.linspace(E_hi, E_lo, n_scan)  # from near-zero downward

    prev_tail = None
    for i, E in enumerate(Es):
        u, n_nodes = numerov_wf(V_arr, E, L)
        tail = u[-1]

        # Only consider states with 0 nodes (ground state)
        if n_nodes == 0 and prev_tail is not None:
            if not np.isnan(tail) and not np.isnan(prev_tail):
                if tail * prev_tail < 0:
                    # Refine with Brent — but verify nodes in the lambda
                    try:
                        def tail_fn(E_val):
                            u2, nn = numerov_wf(V_arr, E_val, L)
                            return u2[-1] if nn == 0 else float('nan')
                        E0 = brentq(lambda e: numerov_wf(V_arr, e, L)[0][-1],
                                    Es[i], Es[i-1], xtol=1e-12)
                        # Verify it's still 0-node
                        _, nn = numerov_wf(V_arr, E0, L)
                        if nn == 0:
                            return E0
                    except (ValueError, RuntimeError):
                        pass
        if n_nodes == 0:
            prev_tail = tail
        else:
            prev_tail = None

    return None

# ======================================================================
# Main
# ======================================================================

print(f"\n{'='*80}")
print("Step 1: Verify Yukawa ground state at known coupling")
print(f"{'='*80}", flush=True)

# At lam=15.11, exact_verify.py found E0=-4.68
lam_test = 15.11
V_test = lam_test * V_yuk_unit
E0_test = find_ground_state(V_test, -20, -1e-6, L=0, n_scan=500)
if E0_test is not None:
    u, nn = numerov_wf(V_test, E0_test)
    print(f"  Yukawa, lam=15.11: E0 = {E0_test:.8f}, nodes = {nn}")
    norm = _trapz(u**2, r)
    r2 = _trapz(u**2 * r**2, r) / norm
    print(f"  <r²> = {r2:.4f}, R_rms = {np.sqrt(r2):.4f}")
else:
    print("  Ground state NOT found")

# ======================================================================
print(f"\n{'='*80}")
print("Step 2: Find exact coupling for E_target")
print(f"{'='*80}", flush=True)

E_targets = [-0.05, -0.50, -2.0, -5.0]

print(f"\n  {'E_tgt':>6}  {'lam_Y':>10}  {'lam_F':>10}  "
      f"{'R_Y':>8}  {'R_F':>8}  {'R_F/R_Y':>8}  {'I_F':>7}")

for E_target in E_targets:
    sys.stdout.flush()
    results = {}

    for name, V_unit in [("Y", V_yuk_unit), ("F", V_fer_unit)]:
        # Bisection on lambda to match ground state to E_target
        def E_ground(log_lam):
            lam = np.exp(log_lam)
            V = lam * V_unit
            E0 = find_ground_state(V, min(E_target * 5, -20), -1e-8, L=0, n_scan=300)
            if E0 is None:
                return 1.0  # no bound state
            return E0 - E_target

        # Find bracket: need lam where ground state exists and is deeper than E_target
        found_bracket = False
        for ll_hi_trial in np.arange(2, 20, 0.5):
            fhi = E_ground(ll_hi_trial)
            if fhi < 0:  # ground state deeper than target
                # Search for lower bound
                for ll_lo_trial in np.arange(ll_hi_trial, -5, -0.5):
                    flo = E_ground(ll_lo_trial)
                    if flo > 0:  # no bound state or shallower
                        try:
                            log_lam = brentq(E_ground, ll_lo_trial, ll_hi_trial, xtol=1e-6)
                            lam_opt = np.exp(log_lam)
                            found_bracket = True
                        except ValueError:
                            pass
                        break
                break

        if not found_bracket:
            results[name] = None
            continue

        # Compute exact wavefunction
        V = lam_opt * V_unit
        E0 = find_ground_state(V, min(E_target * 5, -20), -1e-8, L=0, n_scan=500)
        if E0 is None:
            results[name] = None
            continue

        u, nn = numerov_wf(V, E0, L=0)
        norm = _trapz(u**2, r)
        r2 = _trapz(u**2 * r**2, r) / norm
        R_rms = np.sqrt(r2)
        I_barg = 2.0 * lam_opt * _trapz(r * np.abs(V_unit), r)

        results[name] = {"lam": lam_opt, "E0": E0, "R": R_rms, "I": I_barg}

    if results.get("Y") and results.get("F"):
        Y, F = results["Y"], results["F"]
        ratio = F["R"] / Y["R"]
        print(f"  {E_target:>6.2f}  {Y['lam']:>10.4f}  {F['lam']:>10.4f}  "
              f"{Y['R']:>8.4f}  {F['R']:>8.4f}  {ratio:>8.4f}  {F['I']:>7.3f}")
    else:
        print(f"  {E_target:>6.2f}  "
              f"{'ok' if results.get('Y') else 'fail':>10}  "
              f"{'ok' if results.get('F') else 'fail':>10}")

print(f"\n{'='*80}", flush=True)

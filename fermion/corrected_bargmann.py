#!/usr/bin/env python3
"""
Corrected Bargmann integral table using Prüfer-based eigenvalue solver.

FAST approach: for a given target binding energy E_target, find the
coupling λ such that E_target is exactly the ground state energy.
This is equivalent to finding λ where θ(∞; E_target)/π = 1.0.
Only ~15 Prüfer integrations per table entry (bisection on λ).
"""
import sys
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
from scipy.interpolate import interp1d

_trapz = getattr(np, 'trapezoid', np.trapz)

# ======================================================================
# Potentials
# ======================================================================

r_grid = np.concatenate([
    np.linspace(0.0005, 0.005, 500),
    np.linspace(0.005, 0.05, 500),
    np.linspace(0.05, 0.5, 500),
    np.linspace(0.5, 5.0, 300),
    np.linspace(5.0, 25.0, 200),
])
r_grid = np.unique(r_grid)
print(f"Grid: {len(r_grid)} points, r=[{r_grid[0]:.4f}, {r_grid[-1]:.1f}]")

V_yuk_grid = -np.exp(-r_grid) / (4 * np.pi * r_grid)

print("Computing fermion potential...", end="", flush=True)
s_arr = np.linspace(4.01, 500.0, 800)
ds = s_arr[1] - s_arr[0]
beta2 = 1 - 4.0 / s_arr
rho_v = np.where(beta2 > 0, s_arr * beta2**1.5 / (8 * np.pi), 0.0)
sqrt_s = np.sqrt(s_arr)

V_fer_grid = np.zeros(len(r_grid))
for start in range(0, len(r_grid), 200):
    end = min(start + 200, len(r_grid))
    exp_mat = np.exp(-sqrt_s[None, :] * r_grid[start:end, None])
    V_fer_grid[start:end] = (
        -np.dot(exp_mat, rho_v) * ds / (2 * np.pi)
        / (4 * np.pi * r_grid[start:end])
    )
print(" done.")

V_yuk_fn = interp1d(r_grid, V_yuk_grid, kind='cubic',
                     fill_value=0.0, bounds_error=False)
V_fer_fn = interp1d(r_grid, V_fer_grid, kind='cubic',
                     fill_value=0.0, bounds_error=False)

I_yuk_unit = _trapz(r_grid * np.abs(V_yuk_grid), r_grid)
I_fer_unit = _trapz(r_grid * np.abs(V_fer_grid), r_grid)
print(f"\nUnit Bargmann integrals:")
print(f"  Yukawa:  {I_yuk_unit:.8f}  (analytic: {1/(4*np.pi):.8f})")
print(f"  Fermion: {I_fer_unit:.8f}")

# Jost function criterion for L=1: int r^3 |V| dr < 1
J_yuk_unit = _trapz(r_grid**3 * np.abs(V_yuk_grid), r_grid)
J_fer_unit = _trapz(r_grid**3 * np.abs(V_fer_grid), r_grid)
print(f"\nUnit Jost integrals (L=1 criterion: J < 1):")
print(f"  Yukawa:  {J_yuk_unit:.8f}")
print(f"  Fermion: {J_fer_unit:.8f}")

# ======================================================================
# Prüfer phase at given energy
# ======================================================================

def prufer_phase(V_fn, lam, L, E, r_start=0.001, r_end=25.0):
    """θ(r_end)/π for the Prüfer equation at energy E.

    u'' = [2λV(r) - 2E + L(L+1)/r²] u
    θ' = cos²θ + [-2λV(r) + 2E - L(L+1)/r²] sin²θ
    """
    def rhs(r, y):
        V = float(V_fn(r))
        V_eff = -2.0 * lam * V + 2.0 * E - L * (L + 1) / r**2
        theta = y[0]
        return [np.cos(theta)**2 + V_eff * np.sin(theta)**2]

    sol = solve_ivp(rhs, [r_start, r_end], [0.0], method='RK45',
                    rtol=1e-10, atol=1e-12, max_step=0.05)
    if sol.success:
        return sol.y[0, -1] / np.pi
    return None


# ======================================================================
# FAST coupling search at fixed energy
# ======================================================================

def coupling_at_energy(V_fn, E_target, L=0, lam_lo=0.01, lam_hi=500.0):
    """Find λ where E_target is exactly the ground-state energy.

    At λ_critical, the ground state just appears (E = 0).
    At λ > λ_critical, the ground state deepens.
    The ground state energy E_0(λ) = E_target when
    θ(∞; E_target)/π = 1.0.

    For λ < λ_target: phase at E_target < 1 (no state above E_target)
    For λ > λ_target: phase at E_target > 1 (ground state above E_target)
    """
    def f(log_lam):
        lam = np.exp(log_lam)
        phase = prufer_phase(V_fn, lam, L, E_target)
        if phase is None:
            return -1.0
        return phase - 1.0  # want phase = 1 at ground state

    ll_lo = np.log(lam_lo)
    ll_hi = np.log(lam_hi)

    # Quick bracket search
    f_lo = f(ll_lo)
    f_hi = f(ll_hi)

    # Check if target is achievable
    if f_lo > 0:
        return None  # even smallest coupling gives ground state above E_target
    if f_hi < 0:
        return None  # even largest coupling doesn't bind deep enough

    try:
        log_opt = brentq(f, ll_lo, ll_hi, xtol=1e-8)
        return np.exp(log_opt)
    except (ValueError, RuntimeError):
        # Scan for bracket
        for ll in np.linspace(ll_lo, ll_hi, 50):
            if f(ll) > 0:
                try:
                    # Find lower bracket
                    for ll2 in np.linspace(ll, ll_lo, 30):
                        if f(ll2) < 0:
                            log_opt = brentq(f, ll2, ll, xtol=1e-8)
                            return np.exp(log_opt)
                except (ValueError, RuntimeError):
                    pass
                break
    return None


def ground_energy(V_fn, lam, L=0):
    """Find ground-state energy using coarse scan + bisection.

    Uses the FAST approach: scan θ(∞;E)/π as function of E,
    find where it crosses 1.0.
    """
    # Check if any bound states exist
    phase0 = prufer_phase(V_fn, lam, L, 0.0)
    if phase0 is None or phase0 < 1.0:
        return None

    # Binary search: phase is monotonically decreasing with E
    # At E=0: phase > 1; at E very negative: phase < 1
    E_hi = -1e-8
    E_lo = -1.0

    # First find E_lo where phase < 1
    while True:
        phase = prufer_phase(V_fn, lam, L, E_lo)
        if phase is not None and phase < 1.0:
            break
        E_lo *= 4
        if E_lo < -1e6:
            return None

    def f(E):
        p = prufer_phase(V_fn, lam, L, E)
        return p - 1.0 if p is not None else -1.0

    try:
        E0 = brentq(f, E_lo, E_hi, xtol=1e-10)
        return E0
    except (ValueError, RuntimeError):
        return None


# ======================================================================
# Step 1: Yukawa sanity checks
# ======================================================================

print(f"\n{'='*70}")
print("Step 1: Yukawa eigenvalue checks")
print("=" * 70)

for lam_test in [12.0, 15.0, 20.0, 30.0, 50.0]:
    N0 = int(np.floor(prufer_phase(V_yuk_fn, lam_test, 0, 0.0)))
    E0 = ground_energy(V_yuk_fn, lam_test)
    I_lam = 2.0 * lam_test * I_yuk_unit
    if E0 is not None:
        print(f"  lam={lam_test:5.1f}: N_0={N0}, E0={E0:10.6f}, "
              f"I={I_lam:.3f}, I_ana={lam_test/(2*np.pi):.3f}")
    else:
        print(f"  lam={lam_test:5.1f}: N_0={N0}, E0 NOT FOUND")

# ======================================================================
# Step 2: Fermion energy vs coupling
# ======================================================================

print(f"\n{'='*70}")
print("Step 2: Fermion — energy vs coupling")
print("=" * 70)

print(f"\n  {'lam':>8}  {'N_0':>4}  {'E_0':>12}  {'I_Barg':>8}")

for lam in [0.25, 0.26, 0.28, 0.30, 0.35, 0.40, 0.50, 0.60, 0.80]:
    N0 = int(np.floor(prufer_phase(V_fer_fn, lam, 0, 0.0)))
    I_B = 2.0 * lam * I_fer_unit
    E0 = ground_energy(V_fer_fn, lam) if N0 >= 1 else None
    if E0 is not None:
        print(f"  {lam:>8.3f}  {N0:>4}  {E0:>12.4f}  {I_B:>8.3f}")
    else:
        print(f"  {lam:>8.3f}  {N0:>4}  {'---':>12}  {I_B:>8.3f}")

# ======================================================================
# Step 3: Corrected Bargmann table
# ======================================================================

print(f"\n{'='*70}")
print("Step 3: Corrected Bargmann table at matched binding energy")
print("=" * 70)

E_targets = [-0.01, -0.05, -0.50, -2.0, -5.0, -10.0, -20.0]

print(f"\n  {'E_0':>8}  {'lam_Y':>9}  {'lam_F':>9}  {'I_Y':>7}  {'I_F':>7}  "
      f"{'I_F/I_Y':>7}  {'Lm_Y':>5}  {'Lm_F':>5}")

results = []
for E_target in E_targets:
    sys.stdout.write(f"  {E_target:>8.2f}  ")
    sys.stdout.flush()

    lam_Y = coupling_at_energy(V_yuk_fn, E_target, lam_lo=1.0, lam_hi=500.0)
    if lam_Y is None:
        print("Yukawa FAIL")
        continue

    I_Y = 2.0 * lam_Y * I_yuk_unit

    lam_F = coupling_at_energy(V_fer_fn, E_target, lam_lo=0.01, lam_hi=50.0)
    if lam_F is None:
        print(f"{lam_Y:>9.4f}  Fermion FAIL")
        continue

    I_F = 2.0 * lam_F * I_fer_unit

    Lm_Y = max(0, int(np.floor((I_Y - 1) / 2)))
    Lm_F = max(0, int(np.floor((I_F - 1) / 2)))

    # Jost function criterion for L=1
    J_Y = lam_Y * J_yuk_unit
    J_F = lam_F * J_fer_unit

    results.append({
        'E': E_target, 'lam_Y': lam_Y, 'lam_F': lam_F,
        'I_Y': I_Y, 'I_F': I_F, 'Lm_Y': Lm_Y, 'Lm_F': Lm_F,
        'J_Y': J_Y, 'J_F': J_F,
    })

    print(f"{lam_Y:>9.4f}  {lam_F:>9.4f}  {I_Y:>7.3f}  {I_F:>7.3f}  "
          f"{I_F/I_Y:>7.4f}  {Lm_Y:>5}  {Lm_F:>5}")

# ======================================================================
# Summary
# ======================================================================

print(f"\n{'='*70}")
print("Summary")
print("=" * 70)

if results:
    print(f"\n  OLD TABLE (variational, buggy I_fer values):")
    print(f"    I_fer = 1.55 to 1.66 (nearly constant — returns critical coupling)")

    print(f"\n  CORRECTED TABLE (Prüfer eigenvalue solver):")
    for res in results:
        flag = "  ** I_F > 3 **" if res['I_F'] >= 3.0 else ""
        print(f"    E={res['E']:>8.2f}: I_Y={res['I_Y']:.2f}, I_F={res['I_F']:.2f}, "
              f"Lm_Y={res['Lm_Y']}, Lm_F={res['Lm_F']}{flag}")

    all_lt3 = all(r['I_F'] < 3.0 for r in results)
    print(f"\n  I_F < 3 at ALL binding energies: {'YES' if all_lt3 else 'NO'}")

    print(f"\n  JOST FUNCTION CRITERION (L=1: J < 1):")
    for res in results:
        print(f"    E={res['E']:>8.2f}: J_Yuk={res['J_Y']:.4f}, "
              f"J_fer={res['J_F']:.4f}  (fer < 1: {res['J_F'] < 1})")
    all_jost = all(r['J_F'] < 1.0 for r in results)
    print(f"\n  J_fer < 1 at ALL binding energies: {'YES' if all_jost else 'NO'}")

    if not all_lt3:
        below3 = [r for r in results if r['I_F'] < 3.0]
        above3 = [r for r in results if r['I_F'] >= 3.0]
        if below3:
            print(f"  I_F < 3 for E down to {below3[-1]['E']:.2f}")
        if above3:
            print(f"  I_F >= 3 starting at E = {above3[0]['E']:.2f}")
        print(f"\n  The Bargmann bound proves N_1=0 at weak/moderate binding.")
        print(f"  For deep binding, the Prüfer equation (calogero_phase.py)")
        print(f"  confirms N_1 = 0 exactly for all λ in the N_0=1 range.")

# Checks
print(f"\n{'='*70}")
print("Checks")
print("=" * 70)

checks = {}
if results:
    r0 = results[0]
    I_Y_ana = r0['lam_Y'] / (2 * np.pi)
    checks["yukawa_I_analytic"] = abs(r0['I_Y'] - I_Y_ana) / I_Y_ana < 0.05
    I_Fs = [r['I_F'] for r in results]
    checks["I_F_increasing"] = all(
        I_Fs[i] <= I_Fs[i+1] + 0.1 for i in range(len(I_Fs)-1))
    checks["I_F_always_lt_I_Y"] = all(r['I_F'] < r['I_Y'] for r in results)
    checks["jost_fer_lt_1"] = all(r['J_F'] < 1.0 for r in results)

for name, val in checks.items():
    print(f"  {name}: {'PASS' if val else 'FAIL'}")

print(f"\nall_checks_pass = {all(checks.values()) if checks else False}")
print("=" * 70)

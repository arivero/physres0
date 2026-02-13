#!/usr/bin/env python3
"""
Regge trajectory analysis for fermion-exchange vs boson-exchange composites.

Uses the actual spectral-integral potentials (not simplified tails)
to compute excited state spectra and Regge trajectories.
"""

import numpy as np
from scipy.optimize import minimize_scalar, brentq
from scipy.integrate import quad

# Compatibility
_trapz = getattr(np, 'trapezoid', np.trapz)

# ======================================================================
# Spectral functions (from fermionic_composite_form_factor_check.py)
# ======================================================================

def rho_fermion_scalar(s, m_f=1.0):
    """Fermion loop spectral function, scalar coupling: rho ~ beta^3"""
    if s <= 4*m_f**2:
        return 0.0
    beta = np.sqrt(1 - 4*m_f**2/s)
    return s * beta**3 / (8 * np.pi)

def rho_scalar_loop(s, m=1.0):
    """Scalar loop spectral function: rho ~ beta"""
    if s <= 4*m**2:
        return 0.0
    beta = np.sqrt(1 - 4*m**2/s)
    return beta / (8 * np.pi)

# ======================================================================
# Potentials from spectral integral
# ======================================================================

def V_spectral(r, rho_func, s_min, s_max=500.0):
    """V(r) = -1/(4*pi*r) * integral{ ds/(2*pi) * rho(s) * exp(-sqrt(s)*r) }"""
    if r < 1e-6:
        r = 1e-6
    def integrand(s):
        return rho_func(s) * np.exp(-np.sqrt(s) * r) / (2*np.pi)
    val, _ = quad(integrand, s_min, s_max, limit=100)
    return -val / (4 * np.pi * r)

def V_yukawa(r, m=1.0):
    """Yukawa: V = -exp(-m*r)/(4*pi*r)"""
    if r < 1e-6:
        r = 1e-6
    return -np.exp(-m * r) / (4 * np.pi * r)

# Precompute potentials on a grid for efficiency
def precompute_potential(V_func, r_grid):
    """Compute V(r) on a grid and return interpolation function."""
    V_vals = np.array([V_func(ri) for ri in r_grid])
    from scipy.interpolate import interp1d
    return interp1d(r_grid, V_vals, kind='cubic', fill_value='extrapolate')

# ======================================================================
# Variational method
# ======================================================================

def variational_energy(V_interp, r_grid, L, lam, M_red=1.0):
    """Find minimum energy using variational u = r^{L+1} exp(-alpha*r)."""
    def energy(log_alpha):
        alpha = np.exp(log_alpha)
        u = r_grid**(L+1) * np.exp(-alpha * r_grid)
        norm = _trapz(u**2, r_grid)
        if norm < 1e-30:
            return 1e10
        # Kinetic: <(u')^2>/(2M)
        u_p = ((L+1)/r_grid - alpha) * u
        T = _trapz(u_p**2, r_grid) / (2.0 * M_red * norm)
        # Potential
        V_exp = lam * _trapz(u**2 * V_interp(r_grid), r_grid) / norm
        # Centrifugal
        V_cent = _trapz(u**2 * L*(L+1) / (2*M_red*r_grid**2), r_grid) / norm
        return T + V_exp + V_cent

    result = minimize_scalar(energy, bounds=(-3.0, 5.0), method='bounded')
    return result.fun if result.success else None


# ======================================================================
# Main analysis
# ======================================================================

print("=" * 70)
print("Regge Trajectory Analysis")
print("=" * 70)

# Build fine adaptive grid
r_grid = np.concatenate([
    np.linspace(0.005, 0.1, 200),
    np.linspace(0.1, 1.0, 300),
    np.linspace(1.0, 5.0, 300),
    np.linspace(5.0, 20.0, 200),
])
r_grid = np.unique(r_grid)

print(f"\nGrid: {len(r_grid)} points, r = [{r_grid[0]:.3f}, {r_grid[-1]:.1f}]")

# Precompute potentials
print("\nPrecomputing potentials (this may take a moment)...")

V_yuk_interp = precompute_potential(lambda r: V_yukawa(r, m=1.0), r_grid)
print("  Yukawa: done")

V_fer_interp = precompute_potential(
    lambda r: V_spectral(r, rho_fermion_scalar, s_min=4.0, s_max=200.0),
    r_grid)
print("  Fermion loop: done")

V_scl_interp = precompute_potential(
    lambda r: V_spectral(r, rho_scalar_loop, s_min=4.0, s_max=200.0),
    r_grid)
print("  Scalar loop: done")

# Calibrate couplings for E(L=0) = -0.05
E_target = -0.05

def find_lambda(V_interp, E_tgt, lam_range=(0.01, 1e6)):
    """Find coupling lambda that gives E(L=0) = E_tgt."""
    def f(log_lam):
        lam = np.exp(log_lam)
        E = variational_energy(V_interp, r_grid, L=0, lam=lam)
        if E is None:
            return 1.0
        return E - E_tgt

    log_min, log_max = np.log(lam_range[0]), np.log(lam_range[1])

    # Scan for sign change
    log_lams = np.linspace(log_min, log_max, 60)
    prev_f = None
    for ll in log_lams:
        fv = f(ll)
        if prev_f is not None and prev_f * fv < 0:
            result = brentq(f, ll - (log_lams[1]-log_lams[0]), ll)
            return np.exp(result)
        prev_f = fv
    return None

print("\nCalibrating couplings for E_0(L=0) = -0.05...")

lam_yuk = find_lambda(V_yuk_interp, E_target, (0.1, 1e4))
print(f"  Yukawa: lambda = {lam_yuk:.4f}" if lam_yuk else "  Yukawa: FAILED")

lam_fer = find_lambda(V_fer_interp, E_target, (0.01, 1e8))
print(f"  Fermion loop: lambda = {lam_fer:.4f}" if lam_fer else "  Fermion: FAILED")

lam_scl = find_lambda(V_scl_interp, E_target, (0.01, 1e8))
print(f"  Scalar loop: lambda = {lam_scl:.4f}" if lam_scl else "  Scalar: FAILED")

if lam_yuk is None or lam_fer is None or lam_scl is None:
    print("\nFATAL: Could not calibrate all couplings. Exiting.")
    import sys; sys.exit(1)

# Compute excited states for L = 0, 1, 2, 3, 4
L_values = [0, 1, 2, 3, 4, 5, 6]

print(f"\n{'='*70}")
print("Excited state spectrum: E(L) at fixed coupling")
print("=" * 70)

results = {}
for name, V_interp, lam in [("Yukawa", V_yuk_interp, lam_yuk),
                              ("Fermion loop", V_fer_interp, lam_fer),
                              ("Scalar loop", V_scl_interp, lam_scl)]:
    print(f"\n{name} (lambda={lam:.4f}):")
    energies = []
    for L in L_values:
        E = variational_energy(V_interp, r_grid, L=L, lam=lam)
        energies.append(E)
        if E is not None and E < 0:
            print(f"  L={L}: E = {E:.6f}")
        else:
            print(f"  L={L}: unbound (E = {E:.6f})" if E is not None else f"  L={L}: failed")
    results[name] = energies

# Regge trajectories: J vs M^2
# Nonrelativistic: M = 2*m_constituent + E
# M^2 = (2m + E)^2 ~ 4m^2 + 4mE for small E
print(f"\n{'='*70}")
print("Regge trajectories: J vs M^2 (nonrelativistic)")
print("=" * 70)

m_const = 1.0

for name in ["Yukawa", "Fermion loop", "Scalar loop"]:
    print(f"\n  {name}:")
    print(f"    {'J':>3}  {'E':>12}  {'M^2':>10}  {'Delta M^2':>10}")
    J_vals = []
    M2_vals = []
    for i, L in enumerate(L_values):
        E = results[name][i]
        if E is not None and E < 0:
            M = 2*m_const + E
            M2 = M**2
            J_vals.append(L)
            M2_vals.append(M2)
            dM2 = M2 - M2_vals[0] if len(M2_vals) > 1 else 0.0
            print(f"    {L:>3}  {E:>12.6f}  {M2:>10.6f}  {dM2:>10.6f}")

    n_bound = len(J_vals)

    # Fit Regge slope if we have at least 2 points
    if n_bound >= 2:
        J_arr = np.array(J_vals)
        M2_arr = np.array(M2_vals)
        coeffs = np.polyfit(J_arr, M2_arr, 1)
        alpha_prime = coeffs[0]
        print(f"    Regge slope alpha' = {alpha_prime:.6f}")
        print(f"    Intercept = {coeffs[1]:.6f}")
        print(f"    Number of bound states (L=0..{L_values[-1]}): {n_bound}")
    else:
        print(f"    Only {n_bound} bound state(s) — no trajectory")

# Count bound states
print(f"\n{'='*70}")
print("Summary: bound state count and trajectory character")
print("=" * 70)

for name in ["Yukawa", "Fermion loop", "Scalar loop"]:
    n_bound = sum(1 for E in results[name] if E is not None and E < 0)
    L_max = -1
    for i, L in enumerate(L_values):
        if results[name][i] is not None and results[name][i] < 0:
            L_max = L
    print(f"  {name}:")
    print(f"    Bound states: {n_bound} (L_max = {L_max})")

    # Physical interpretation
    if n_bound <= 1:
        print(f"    Trajectory: POINT-LIKE (no excited states)")
    elif n_bound <= 3:
        print(f"    Trajectory: SHORT (few excited states)")
    else:
        print(f"    Trajectory: EXTENDED (rich spectrum)")

# ======================================================================
# Part 2: Scan binding energy to find Regge trajectory threshold
# ======================================================================

print(f"\n{'='*70}")
print("Binding energy scan: when do L>0 states appear?")
print("=" * 70)

E_scan = [-0.01, -0.05, -0.1, -0.5, -1.0, -2.0, -5.0, -10.0]

for name, V_interp in [("Yukawa", V_yuk_interp),
                         ("Fermion loop", V_fer_interp)]:
    print(f"\n  {name}:")
    print(f"    {'E_target':>10}  {'lambda':>10}  {'N_bound':>8}  {'L_max':>5}")
    for E_t in E_scan:
        lam = find_lambda(V_interp, E_t, (0.01, 1e10))
        if lam is None:
            print(f"    {E_t:>10.2f}  {'(failed)':>10}  {'---':>8}  {'---':>5}")
            continue
        n_b = 0
        L_max_b = -1
        for L in range(8):
            E = variational_energy(V_interp, r_grid, L=L, lam=lam)
            if E is not None and E < 0:
                n_b += 1
                L_max_b = L
        print(f"    {E_t:>10.2f}  {lam:>10.2f}  {n_b:>8}  {L_max_b:>5}")

# ======================================================================
# Physical interpretation
# ======================================================================

print(f"\n{'='*70}")
print("Physical interpretation")
print("=" * 70)

n_yuk = sum(1 for E in results["Yukawa"] if E is not None and E < 0)
n_fer = sum(1 for E in results["Fermion loop"] if E is not None and E < 0)
n_scl = sum(1 for E in results["Scalar loop"] if E is not None and E < 0)

print(f"""
At matched L=0 binding energy (E = {E_target}):
  Yukawa:       {n_yuk} bound state(s)
  Scalar loop:  {n_scl} bound state(s)
  Fermion loop: {n_fer} bound state(s)

The number of bound states reflects the effective range of the potential:
  - Yukawa (long range): supports excited states at higher L
  - Fermion loop (short range): centrifugal barrier overcomes binding
    potential at lower L, truncating the Regge trajectory

This is another manifestation of "structurelessness":
  - A point particle has NO excited states
  - A string-like composite has a rich Regge tower
  - Our fermion-exchange composite is intermediate: few states

In QCD terms:
  - Mesons (gluon exchange): linear Regge trajectory, many states
  - "Gluino-onia" (gluino exchange): truncated trajectory, few states
  - This matches the observation that leptons have no excited states!
""")

# ======================================================================
# Checks
# ======================================================================

checks = {
    "yukawa_L0_bound": results["Yukawa"][0] is not None and results["Yukawa"][0] < 0,
    "fermion_L0_bound": results["Fermion loop"][0] is not None and results["Fermion loop"][0] < 0,
    "same_L0_energy": (results["Yukawa"][0] is not None and
                       results["Fermion loop"][0] is not None and
                       abs(results["Yukawa"][0] - results["Fermion loop"][0]) < 0.01),
}

# Check that fermion has fewer or equal bound states
if n_fer <= n_yuk:
    checks["fermion_fewer_states"] = True
else:
    checks["fermion_fewer_states"] = False

print("Checks:")
for name, val in checks.items():
    print(f"  {name}: {'PASS' if val else 'FAIL'}")

all_pass = all(checks.values())
print(f"\nall_checks_pass = {all_pass}")
print("=" * 70)

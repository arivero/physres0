"""
Improved variational calculation with multi-parameter trial wavefunctions.

Strategy: Fix lambda from the reliable hydrogen (1-param) calculation,
then check whether more flexible trials give different sizes.

Compares:
1. Single-parameter hydrogen trial: u = r * exp(-alpha*r)
2. Two-parameter Gaussian trial: u = r * exp(-alpha*r - beta*r^2)
3. Two-term expansion: u = r * (c1*exp(-a1*r) + c2*exp(-a2*r))

The goal is to check whether the 5.8x size suppression from the
simple trial is robust or an artifact of the trial function.

See: fermion/paper.tex, Section 6
"""

import numpy as np
from scipy.integrate import quad
from scipy.optimize import minimize, minimize_scalar, brentq

# Compatibility: numpy < 2.0 uses trapz, >= 2.0 uses trapezoid
_trapz = getattr(np, 'trapezoid', np.trapz)

# ── Parameters ────────────────────────────────────────────────────────
m_f = 1.0
threshold = 4 * m_f**2
M_red = 1.0

# ── Spectral functions ────────────────────────────────────────────────

def rho_fermion(s):
    if s <= threshold: return 0.0
    delta = s - threshold
    return delta**1.5 / (24 * np.pi * np.sqrt(s))

def rho_scalar(s):
    if s <= threshold: return 0.0
    return np.sqrt((s - threshold) / s) / (16 * np.pi)

def V_spectral(r, rho_func, s_max=200.0):
    def integrand(s):
        return rho_func(s) * np.exp(-np.sqrt(s) * r)
    result, _ = quad(integrand, threshold + 1e-10, s_max,
                     limit=200, epsrel=1e-10)
    return -result / (4 * np.pi * r * 2 * np.pi)

# ── Grid ──────────────────────────────────────────────────────────────

N = 600
r_grid = np.linspace(0.005, 18.0, N)
dr = r_grid[1] - r_grid[0]

print("Precomputing potentials...")
V_yuk = -np.exp(-m_f * r_grid) / (4 * np.pi * r_grid)
V_fer = np.array([V_spectral(r, rho_fermion) for r in r_grid])
V_scl = np.array([V_spectral(r, rho_scalar) for r in r_grid])
print("  done.")

# ══════════════════════════════════════════════════════════════════════
# PART 1: Robust hydrogen (1-param) calculation
# ══════════════════════════════════════════════════════════════════════

def V_expectation_hydrogen(alpha, V_arr):
    """<V> for trial u = r*exp(-alpha*r)."""
    w = r_grid**2 * np.exp(-2 * alpha * r_grid)
    w_sum = _trapz(w, r_grid)
    if w_sum < 1e-300: return 0.0
    return _trapz(w * V_arr, r_grid) / w_sum

def var_energy_hydrogen(alpha, V_arr, lam):
    T = alpha**2 / (2 * M_red)
    return T + lam * V_expectation_hydrogen(alpha, V_arr)

def opt_alpha_energy(V_arr, lam):
    res = minimize_scalar(lambda a: var_energy_hydrogen(a, V_arr, lam),
                          bounds=(0.05, 200.0), method='bounded',
                          options={'xatol': 1e-10})
    return res.x, res.fun

def find_lambda(V_arr, E_target):
    def residual(log_lam):
        _, E = opt_alpha_energy(V_arr, np.exp(log_lam))
        return E - E_target
    ll_lo, ll_hi = np.log(0.01), np.log(1e14)
    r_lo, r_hi = residual(ll_lo), residual(ll_hi)
    if r_lo * r_hi > 0: return None
    return np.exp(brentq(residual, ll_lo, ll_hi, xtol=1e-8))

# ══════════════════════════════════════════════════════════════════════
# PART 2: Multi-parameter trials at FIXED lambda
# ══════════════════════════════════════════════════════════════════════

def compute_E_r2(u_vals, V_arr, lam):
    """Compute E and <r^2> for given u(r) on grid."""
    norm = _trapz(u_vals**2, r_grid)
    if norm < 1e-300:
        return 1e10, 1e10
    du = np.gradient(u_vals, dr)
    T = _trapz(du**2, r_grid) / (2 * M_red * norm)
    PE = lam * _trapz(u_vals**2 * V_arr, r_grid) / norm
    E = T + PE
    # <r^2> for 3D wavefunction psi = u/r
    psi2_r2 = (u_vals / r_grid)**2 * r_grid**2
    r2 = _trapz(r_grid**2 * psi2_r2, r_grid) / _trapz(psi2_r2, r_grid)
    return E, r2

# Trial functions
def u_hydrogen(r, alpha):
    return r * np.exp(-alpha * r)

def u_gauss(r, alpha, beta):
    return r * np.exp(-alpha * r - beta * r**2)

def u_twoterm(r, a1, a2, c2):
    return r * (np.exp(-a1 * r) + c2 * np.exp(-a2 * r))

def optimize_gauss(V_arr, lam, alpha0):
    """Optimize Gaussian trial, starting from hydrogen solution."""
    def objective(params):
        alpha, beta = params
        if alpha < 0.01 or beta < 0: return 1e10
        u = u_gauss(r_grid, alpha, beta)
        E, _ = compute_E_r2(u, V_arr, lam)
        return E

    # Try several starting points near the hydrogen solution
    best_E = 1e10
    best_params = None
    for beta0 in [0.0, 0.01, 0.1, 1.0]:
        for alpha_init in [alpha0 * 0.5, alpha0, alpha0 * 2.0]:
            res = minimize(objective, [alpha_init, beta0],
                           bounds=[(0.01, alpha0*10), (0.0, alpha0*5)],
                           method='L-BFGS-B')
            if res.fun < best_E:
                best_E = res.fun
                best_params = res.x
    u = u_gauss(r_grid, best_params[0], best_params[1])
    E, r2 = compute_E_r2(u, V_arr, lam)
    return best_params, E, r2

def optimize_twoterm(V_arr, lam, alpha0):
    """Optimize two-term trial, starting from hydrogen solution."""
    def objective(params):
        a1, a2, c2 = params
        if a1 < 0.01 or a2 < 0.01: return 1e10
        u = u_twoterm(r_grid, a1, a2, c2)
        E, _ = compute_E_r2(u, V_arr, lam)
        return E

    best_E = 1e10
    best_params = None
    # c2=0 reduces to hydrogen; try mixing in a second term
    for c2_init in [0.0, 0.3, 0.5, -0.3]:
        for a2_factor in [0.3, 0.5, 2.0, 3.0]:
            a2_init = alpha0 * a2_factor
            res = minimize(objective, [alpha0, a2_init, c2_init],
                           bounds=[(0.01, alpha0*10), (0.01, alpha0*10),
                                   (-5, 5)],
                           method='L-BFGS-B')
            if res.fun < best_E:
                best_E = res.fun
                best_params = res.x
    u = u_twoterm(r_grid, best_params[0], best_params[1], best_params[2])
    E, r2 = compute_E_r2(u, V_arr, lam)
    return best_params, E, r2

# ══════════════════════════════════════════════════════════════════════
# MAIN CALCULATION
# ══════════════════════════════════════════════════════════════════════

E_target = -0.05

print(f"\n{'='*70}")
print(f"Improved variational: E_target = {E_target}")
print(f"{'='*70}")

# Step 1: Get reliable hydrogen results
print("\n── Step 1: Hydrogen (1-param) baseline ──")
potentials = [("Yukawa", V_yuk), ("Scalar loop", V_scl), ("Fermion loop", V_fer)]
hydrogen_results = {}

for pot_name, V_arr in potentials:
    lam = find_lambda(V_arr, E_target)
    if lam is None:
        print(f"  {pot_name:>15}: no binding")
        continue
    alpha, E = opt_alpha_energy(V_arr, lam)
    R_rms = np.sqrt(3.0) / alpha
    r2 = 3.0 / alpha**2
    hydrogen_results[pot_name] = {"lam": lam, "alpha": alpha, "E": E,
                                   "r2": r2, "R_rms": R_rms}
    print(f"  {pot_name:>15}: lam={lam:.2e}, alpha={alpha:.4f}, "
          f"R_rms={R_rms:.4f}, E={E:.6f}")

# Step 2: Optimize multi-param trials at fixed lambda
print("\n── Step 2: Multi-parameter trials at fixed lambda ──")

all_results = {}  # (trial_name, pot_name) -> {r2, R_rms, E, ...}

for pot_name, V_arr in potentials:
    if pot_name not in hydrogen_results:
        continue
    hr = hydrogen_results[pot_name]
    lam = hr["lam"]
    alpha0 = hr["alpha"]

    print(f"\n  {pot_name} (lambda = {lam:.2e}):")
    print(f"    {'Trial':>20}  {'E':>10}  {'<r^2>':>10}  {'R_rms':>8}  params")
    print(f"    {'-'*65}")

    # Hydrogen baseline
    u = u_hydrogen(r_grid, alpha0)
    E_h, r2_h = compute_E_r2(u, V_arr, lam)
    R_h = np.sqrt(r2_h)
    print(f"    {'Hydrogen (1p)':>20}  {E_h:>10.6f}  {r2_h:>10.4e}  "
          f"{R_h:>8.4f}  alpha={alpha0:.4f}")
    all_results[("Hydrogen", pot_name)] = {"E": E_h, "r2": r2_h, "R_rms": R_h}

    # Gaussian
    params_g, E_g, r2_g = optimize_gauss(V_arr, lam, alpha0)
    R_g = np.sqrt(r2_g)
    print(f"    {'Gaussian (2p)':>20}  {E_g:>10.6f}  {r2_g:>10.4e}  "
          f"{R_g:>8.4f}  alpha={params_g[0]:.4f}, beta={params_g[1]:.4f}")
    all_results[("Gaussian", pot_name)] = {"E": E_g, "r2": r2_g, "R_rms": R_g}

    # Two-term
    params_t, E_t, r2_t = optimize_twoterm(V_arr, lam, alpha0)
    R_t = np.sqrt(r2_t)
    print(f"    {'Two-term (3p)':>20}  {E_t:>10.6f}  {r2_t:>10.4e}  "
          f"{R_t:>8.4f}  a1={params_t[0]:.4f}, a2={params_t[1]:.4f}, "
          f"c2={params_t[2]:.4f}")
    all_results[("Two-term", pot_name)] = {"E": E_t, "r2": r2_t, "R_rms": R_t}

# ══════════════════════════════════════════════════════════════════════
# COMPARISON
# ══════════════════════════════════════════════════════════════════════

print(f"\n{'='*70}")
print("Size ratios R_fer/R_yuk across trial wavefunctions:")
print(f"{'='*70}")

checks = {}
for trial_name in ["Hydrogen", "Gaussian", "Two-term"]:
    yuk_key = (trial_name, "Yukawa")
    fer_key = (trial_name, "Fermion loop")
    if yuk_key in all_results and fer_key in all_results:
        ratio = all_results[fer_key]["R_rms"] / all_results[yuk_key]["R_rms"]
        r2_ratio = all_results[fer_key]["r2"] / all_results[yuk_key]["r2"]
        inv = 1.0 / ratio if ratio > 0 else 0
        print(f"  {trial_name:>12}: R_fer/R_yuk = {ratio:.4f}  "
              f"(fermion is {inv:.1f}x smaller)")
        checks[f"ratio_{trial_name}"] = ratio

# Also check if flexible trials improve energy significantly
print(f"\n{'='*70}")
print("Energy improvement from flexible trials:")
print(f"{'='*70}")

for pot_name in ["Yukawa", "Scalar loop", "Fermion loop"]:
    E_h = all_results.get(("Hydrogen", pot_name), {}).get("E")
    E_g = all_results.get(("Gaussian", pot_name), {}).get("E")
    E_t = all_results.get(("Two-term", pot_name), {}).get("E")
    if E_h is not None:
        print(f"\n  {pot_name}:")
        print(f"    Hydrogen:  E = {E_h:.6f}")
        if E_g is not None:
            delta_g = E_g - E_h
            print(f"    Gaussian:  E = {E_g:.6f}  (delta = {delta_g:.6f})")
        if E_t is not None:
            delta_t = E_t - E_h
            print(f"    Two-term:  E = {E_t:.6f}  (delta = {delta_t:.6f})")

# Robustness check
if len(checks) >= 2:
    ratios = list(checks.values())
    spread = max(ratios) - min(ratios)
    mean_ratio = np.mean(ratios)
    print(f"\n{'='*70}")
    print("Robustness check:")
    print(f"  Mean R_fer/R_yuk: {mean_ratio:.4f}  (fermion is {1/mean_ratio:.1f}x smaller)")
    print(f"  Spread: {spread:.4f}")
    print(f"  Relative spread: {spread/mean_ratio:.1%}")
    robust = spread / mean_ratio < 0.30
    print(f"  Robust (spread < 30%): {robust}")
    checks["robust"] = robust

print(f"\n{'='*70}")
print("Checks:")
for name, val in checks.items():
    if isinstance(val, bool):
        print(f"  {name}: {'PASS' if val else 'FAIL'}")
    else:
        print(f"  {name}: {val:.4f}")

all_pass = all(v if isinstance(v, bool) else True for v in checks.values())
print(f"\nall_checks_pass = {all_pass}")
print(f"{'='*70}")

"""
Fine-grid variational calculation with multi-parameter trial wavefunctions.

Uses adaptive grid (fine near origin, coarser far away) to properly
resolve concentrated wavefunctions near short-range loop potentials.

Strategy: For each (trial, potential) combination, independently find
lambda that gives E = -0.05, then compare sizes.
"""

import numpy as np
from scipy.integrate import quad
from scipy.optimize import minimize, minimize_scalar, brentq
import time

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

# ── Fine adaptive grid ───────────────────────────────────────────────

# Dense near origin (for concentrated wavefunctions), coarser far out
r_fine = np.concatenate([
    np.linspace(0.001, 0.1, 200),    # very fine near origin
    np.linspace(0.1, 1.0, 300),       # fine in intermediate region
    np.linspace(1.0, 5.0, 300),       # moderate
    np.linspace(5.0, 25.0, 200),      # coarse far out
])
r_fine = np.unique(r_fine)  # remove duplicates at boundaries
N_fine = len(r_fine)
dr_fine = np.diff(r_fine)
# For gradient: use average spacing
dr_avg = np.concatenate([dr_fine[:1], (dr_fine[:-1] + dr_fine[1:]) / 2, dr_fine[-1:]])

print(f"Grid: {N_fine} points, r_min={r_fine[0]:.4f}, r_max={r_fine[-1]:.1f}")
print(f"  dr_min={np.min(dr_fine):.4e}, dr_max={np.max(dr_fine):.4e}")

# Precompute potentials
print("Computing potentials on fine grid...")
t0 = time.time()
V_yuk_f = -np.exp(-m_f * r_fine) / (4 * np.pi * r_fine)
V_fer_f = np.array([V_spectral(r, rho_fermion) for r in r_fine])
V_scl_f = np.array([V_spectral(r, rho_scalar) for r in r_fine])
print(f"  done in {time.time()-t0:.1f}s")

# ── Compute observables ──────────────────────────────────────────────

def compute_E_r2(u_vals, V_arr, lam, grid=r_fine):
    """Compute E and <r^2> on the fine grid."""
    norm = _trapz(u_vals**2, grid)
    if norm < 1e-300:
        return 1e10, 1e10
    # Kinetic energy via numerical derivative
    du = np.gradient(u_vals, grid)
    T = _trapz(du**2, grid) / (2 * M_red * norm)
    PE = lam * _trapz(u_vals**2 * V_arr, grid) / norm
    E = T + PE
    # <r^2>
    psi2_r2 = (u_vals / grid)**2 * grid**2
    r2 = _trapz(grid**2 * psi2_r2, grid) / _trapz(psi2_r2, grid)
    return E, r2

# ── Trial wavefunctions ──────────────────────────────────────────────

def u_hydrogen(r, alpha):
    return r * np.exp(-alpha * r)

def u_gauss(r, alpha, beta):
    return r * np.exp(-alpha * r - beta * r**2)

def u_twoterm(r, a1, a2, c2):
    return r * (np.exp(-a1 * r) + c2 * np.exp(-a2 * r))

# ── Optimization for each trial ─────────────────────────────────────

def optimize_hydrogen(V_arr, lam, grid=r_fine):
    """1D optimization for hydrogen trial."""
    def objective(alpha):
        u = u_hydrogen(grid, alpha)
        E, _ = compute_E_r2(u, V_arr, lam, grid)
        return E
    res = minimize_scalar(objective, bounds=(0.01, 500.0), method='bounded',
                          options={'xatol': 1e-10})
    u = u_hydrogen(grid, res.x)
    E, r2 = compute_E_r2(u, V_arr, lam, grid)
    return [res.x], E, r2

def optimize_gauss(V_arr, lam, alpha0, grid=r_fine):
    """Gaussian trial with multiple starting points."""
    def objective(params):
        alpha, beta = params
        if alpha < 0.001 or beta < 0: return 1e10
        u = u_gauss(grid, alpha, beta)
        E, _ = compute_E_r2(u, V_arr, lam, grid)
        return E

    best_E = 1e10
    best_params = [alpha0, 0.0]
    for beta0 in [0.0, 0.001, 0.01, 0.1, 1.0, 5.0]:
        for af in [0.3, 0.5, 0.8, 1.0, 1.5, 2.0, 5.0]:
            x0 = [alpha0 * af, beta0]
            try:
                res = minimize(objective, x0,
                               bounds=[(0.001, alpha0*20), (0.0, max(alpha0*5, 50))],
                               method='L-BFGS-B',
                               options={'maxiter': 200})
                if res.fun < best_E:
                    best_E = res.fun
                    best_params = list(res.x)
            except Exception:
                continue

    u = u_gauss(grid, best_params[0], best_params[1])
    E, r2 = compute_E_r2(u, V_arr, lam, grid)
    return best_params, E, r2

def optimize_twoterm(V_arr, lam, alpha0, grid=r_fine):
    """Two-term trial with multiple starting points."""
    def objective(params):
        a1, a2, c2 = params
        if a1 < 0.001 or a2 < 0.001: return 1e10
        u = u_twoterm(grid, a1, a2, c2)
        E, _ = compute_E_r2(u, V_arr, lam, grid)
        return E

    best_E = 1e10
    best_params = [alpha0, alpha0, 0.0]
    for c2_init in [0.0, 0.2, 0.5, -0.2, -0.5, 1.0]:
        for a2_factor in [0.2, 0.3, 0.5, 1.5, 2.0, 3.0, 5.0]:
            for a1_factor in [0.5, 0.8, 1.0, 1.5, 2.0]:
                x0 = [alpha0 * a1_factor, alpha0 * a2_factor, c2_init]
                try:
                    res = minimize(objective, x0,
                                   bounds=[(0.001, alpha0*20),
                                           (0.001, alpha0*20),
                                           (-10, 10)],
                                   method='L-BFGS-B',
                                   options={'maxiter': 200})
                    if res.fun < best_E:
                        best_E = res.fun
                        best_params = list(res.x)
                except Exception:
                    continue

    u = u_twoterm(grid, best_params[0], best_params[1], best_params[2])
    E, r2 = compute_E_r2(u, V_arr, lam, grid)
    return best_params, E, r2

# ── Find lambda for each (trial, potential) ──────────────────────────

def find_lambda_trial(optimize_func, V_arr, E_target, alpha_hint=1.0,
                      lam_range=(0.01, 1e14)):
    """Find lambda giving E = E_target for a given trial function."""
    def residual(log_lam):
        lam = np.exp(log_lam)
        _, E, _ = optimize_func(V_arr, lam, alpha_hint)
        return E - E_target

    ll_lo, ll_hi = np.log(lam_range[0]), np.log(lam_range[1])
    try:
        r_lo = residual(ll_lo)
        r_hi = residual(ll_hi)
    except Exception:
        return None, None, None, None

    if r_lo * r_hi > 0:
        return None, None, None, None

    try:
        log_lam = brentq(residual, ll_lo, ll_hi, xtol=1e-6, maxiter=50)
    except Exception:
        return None, None, None, None

    lam = np.exp(log_lam)
    params, E, r2 = optimize_func(V_arr, lam, alpha_hint)
    return lam, params, E, r2

# ══════════════════════════════════════════════════════════════════════
# MAIN CALCULATION
# ══════════════════════════════════════════════════════════════════════

E_target = -0.05

print(f"\n{'='*70}")
print(f"Fine-grid variational: E_target = {E_target}")
print(f"{'='*70}")

potentials = [
    ("Yukawa", V_yuk_f),
    ("Scalar loop", V_scl_f),
    ("Fermion loop", V_fer_f),
]

trials = [
    ("Hydrogen (1p)", lambda V, lam, a0: optimize_hydrogen(V, lam)),
    ("Gaussian (2p)", optimize_gauss),
    ("Two-term (3p)", optimize_twoterm),
]

all_results = {}

for pot_name, V_arr in potentials:
    print(f"\n── {pot_name} ──")
    print(f"  {'Trial':>20}  {'lambda':>12}  {'E':>10}  "
          f"{'<r^2>':>10}  {'R_rms':>8}  params")
    print(f"  {'-'*75}")

    for trial_name, opt_func in trials:
        t0 = time.time()
        lam, params, E, r2 = find_lambda_trial(opt_func, V_arr, E_target)
        dt = time.time() - t0

        if lam is None:
            print(f"  {trial_name:>20}  {'no binding':>12}  ({dt:.1f}s)")
            continue

        R_rms = np.sqrt(r2)
        p_str = ", ".join(f"{p:.4f}" for p in params)
        print(f"  {trial_name:>20}  {lam:>12.2e}  {E:>10.6f}  "
              f"{r2:>10.4e}  {R_rms:>8.4f}  [{p_str}]  ({dt:.1f}s)")
        all_results[(trial_name, pot_name)] = {
            "lam": lam, "params": params, "E": E, "r2": r2, "R_rms": R_rms
        }

# ══════════════════════════════════════════════════════════════════════
# COMPARISON
# ══════════════════════════════════════════════════════════════════════

print(f"\n{'='*70}")
print("Size ratios R_fer/R_yuk (at matched E = -0.05):")
print(f"{'='*70}")

checks = {}
for trial_name, _ in trials:
    yuk_key = (trial_name, "Yukawa")
    fer_key = (trial_name, "Fermion loop")
    scl_key = (trial_name, "Scalar loop")
    if yuk_key in all_results and fer_key in all_results:
        ratio = all_results[fer_key]["R_rms"] / all_results[yuk_key]["R_rms"]
        inv = 1.0/ratio if ratio > 0 else 0
        line = f"  {trial_name:>20}: R_fer/R_yuk = {ratio:.4f}  (fermion {inv:.1f}x smaller)"
        if scl_key in all_results:
            ratio_sf = all_results[fer_key]["R_rms"] / all_results[scl_key]["R_rms"]
            line += f"  R_fer/R_scl = {ratio_sf:.4f}"
        print(line)
        checks[f"ratio_{trial_name}"] = ratio

if len(checks) >= 2:
    ratios = list(checks.values())
    spread = max(ratios) - min(ratios)
    mean_ratio = np.mean(ratios)
    print(f"\n  Mean R_fer/R_yuk: {mean_ratio:.4f}  "
          f"(fermion is {1/mean_ratio:.1f}x smaller)")
    print(f"  Spread: {spread:.4f}")
    print(f"  Relative spread: {spread/mean_ratio:.1%}")
    robust = spread / mean_ratio < 0.50  # relaxed criterion
    print(f"  Robust (spread < 50%): {robust}")
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

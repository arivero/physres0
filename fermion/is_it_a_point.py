"""
Is a fermionic composite a point?  (at current experimental limits)

Model: two scalar bosons bound by fermionic exchange (one-loop).
Uses variational method with trial u(r) = r*exp(-alpha*r).

Computes charge radii at matched binding energy for:
  1. Yukawa potential (tree-level single boson exchange)
  2. Scalar-loop potential (scalar pair exchange)
  3. Fermion-loop potential (fermion pair exchange, scalar coupling)

Compares to experimental limits on muon compositeness.

See: fermion/2026-02-13-fermionic-composite-form-factor-suppression.md
"""

import numpy as np
from scipy.integrate import quad
from scipy.optimize import minimize_scalar, brentq

# ── Physical constants ────────────────────────────────────────────────
hbar_c = 197.3269804      # MeV·fm
m_mu   = 105.6583755      # MeV
m_pi   = 139.57039        # MeV
r_pi   = 0.659            # fm  (pion charge radius, PDG 2024)

# Experimental muon compositeness limit (LEP contact interaction)
Lambda_mu = 8000.0         # MeV  (conservative: Lambda > 8 TeV)
r_mu_limit = hbar_c / Lambda_mu   # fm
r2_mu_limit = r_mu_limit**2       # fm^2

print("=" * 70)
print("Is a fermionic composite a point?")
print("=" * 70)
print(f"\n  Pion charge radius:          r_pi   = {r_pi:.3f} fm")
print(f"  Muon compositeness limit:    Lambda > {Lambda_mu/1000:.0f} TeV")
print(f"    =>  r_mu < {r_mu_limit:.4f} fm  = {r_mu_limit*1e3:.2f} am")
print(f"    =>  <r^2> < {r2_mu_limit:.2e} fm^2")

# ── Natural units (m_f = 1) ───────────────────────────────────────────
m_f = 1.0
threshold = 4 * m_f**2
M_red = 1.0   # reduced mass of two-boson system

# ── Spectral functions (unit coupling) ────────────────────────────────

def rho_fermion(s):
    """Fermion loop, scalar coupling (3P0). rho ~ delta^{3/2}."""
    if s <= threshold:
        return 0.0
    delta = s - threshold
    return delta**1.5 / (24 * np.pi * np.sqrt(s))

def rho_scalar(s):
    """Scalar loop. rho ~ delta^{1/2}."""
    if s <= threshold:
        return 0.0
    return np.sqrt((s - threshold) / s) / (16 * np.pi)

def V_spectral(r, rho_func, s_max=200.0):
    """V(r) from Kallen-Lehmann spectral integral. Finite everywhere."""
    def integrand(s):
        return rho_func(s) * np.exp(-np.sqrt(s) * r)
    result, _ = quad(integrand, threshold + 1e-10, s_max,
                     limit=200, epsrel=1e-10)
    return -result / (4 * np.pi * r * 2 * np.pi)

# ── Precompute potentials on grid ─────────────────────────────────────

N_pot = 400
r_grid = np.linspace(0.01, 20.0, N_pot)
dr = r_grid[1] - r_grid[0]

print("\nPrecomputing potentials on grid...")

# Yukawa (tree-level single boson, mass = m_f)
V_yuk = -np.exp(-m_f * r_grid) / (4 * np.pi * r_grid)

# Fermion loop (scalar coupling) — physical, finite at origin
V_fer = np.array([V_spectral(r, rho_fermion) for r in r_grid])

# Scalar loop — physical, finite at origin
V_scl = np.array([V_spectral(r, rho_scalar) for r in r_grid])

print("  done.")

# Print potential values at selected r for reference
print("\n  Potential values (unit coupling):")
print(f"  {'r':>5}  {'V_Yukawa':>12}  {'V_fermion':>12}  {'V_scalar':>12}")
for r_val in [0.1, 0.5, 1.0, 2.0, 5.0]:
    idx = np.argmin(np.abs(r_grid - r_val))
    print(f"  {r_grid[idx]:>5.2f}  {V_yuk[idx]:>12.4e}  "
          f"{V_fer[idx]:>12.4e}  {V_scl[idx]:>12.4e}")

# ══════════════════════════════════════════════════════════════════════
# VARIATIONAL METHOD
#
# Trial: u(r) = r * exp(-alpha * r)
# Analytic results:
#   <T>   = alpha^2 / (2*M_red)
#   <r^2> = 3 / alpha^2
#   F1(q) = [1 / (1 + q^2/(4*alpha^2))]^2   (dipole form factor)
#
# <V> computed numerically: 4*alpha^3 * integral(r^2 * exp(-2*alpha*r) * V(r) dr)
# ══════════════════════════════════════════════════════════════════════

def V_expectation(alpha, V_arr):
    """<V> for trial u = r*exp(-alpha*r) in potential V(r)."""
    w = r_grid**2 * np.exp(-2 * alpha * r_grid)
    w_sum = np.trapezoid(w, r_grid)
    if w_sum < 1e-300:
        return 0.0
    return np.trapezoid(w * V_arr, r_grid) / w_sum

def var_energy(alpha, V_arr, lam):
    """Variational energy E(alpha) = T + lam*<V>."""
    T = alpha**2 / (2 * M_red)
    Vexp = V_expectation(alpha, V_arr)
    return T + lam * Vexp

def opt_alpha_energy(V_arr, lam, alpha_range=(0.05, 200.0)):
    """Find optimal alpha minimizing E, return (alpha_opt, E_opt)."""
    res = minimize_scalar(
        lambda a: var_energy(a, V_arr, lam),
        bounds=alpha_range, method='bounded',
        options={'xatol': 1e-10}
    )
    return res.x, res.fun

def find_lambda(V_arr, E_target, lam_range=(1.0, 1e10)):
    """Find coupling lam such that E_opt(lam) = E_target."""
    def residual(log_lam):
        lam = np.exp(log_lam)
        _, E = opt_alpha_energy(V_arr, lam)
        return E - E_target

    ll_lo, ll_hi = np.log(lam_range[0]), np.log(lam_range[1])
    r_lo = residual(ll_lo)
    r_hi = residual(ll_hi)

    if r_lo < 0:
        # Already bound at lowest lambda — extend range down
        ll_lo = np.log(0.01)
        r_lo = residual(ll_lo)
    if r_hi > 0:
        # Still not bound at highest lambda — extend range up
        ll_hi = np.log(1e14)
        r_hi = residual(ll_hi)

    if r_lo * r_hi > 0:
        return None  # no sign change

    log_lam = brentq(residual, ll_lo, ll_hi, xtol=1e-8)
    return np.exp(log_lam)

# ══════════════════════════════════════════════════════════════════════
# MAIN CALCULATION
# ══════════════════════════════════════════════════════════════════════

print("\n" + "=" * 70)
print("Variational bound-state calculation")
print("=" * 70)

E_targets = [-0.01, -0.05, -0.1, -0.5]

checks = {}

for E_target in E_targets:
    print(f"\n── Binding energy E = {E_target} ──")

    cases = [
        (V_yuk, "Yukawa (tree boson)"),
        (V_scl, "Scalar loop"),
        (V_fer, "Fermion loop"),
    ]

    print(f"\n  {'Case':>25}  {'lambda':>12}  {'alpha':>8}  "
          f"{'R_rms':>8}  {'<r^2>':>10}  {'q_1%':>8}")
    print("  " + "-" * 80)

    row = {}
    for V_arr, label in cases:
        lam = find_lambda(V_arr, E_target)
        if lam is None:
            print(f"  {label:>25}  {'no binding':>12}")
            continue
        alpha, E = opt_alpha_energy(V_arr, lam)
        R_rms = np.sqrt(3.0) / alpha  # analytic for this trial
        r2 = 3.0 / alpha**2
        # Dipole form factor: F1(q) = [1/(1+q^2/(4*alpha^2))]^2
        # |F1-1| = 0.01 when q^2/(4*alpha^2) = 1/sqrt(0.99) - 1 ≈ 0.005025
        q_1pct = alpha * np.sqrt(4 * (1.0 / np.sqrt(0.99) - 1))

        row[label] = {
            "lam": lam, "alpha": alpha, "E": E,
            "R_rms": R_rms, "r2": r2, "q_1pct": q_1pct
        }
        print(f"  {label:>25}  {lam:>12.2e}  {alpha:>8.3f}  "
              f"{R_rms:>8.4f}  {r2:>10.4e}  {q_1pct:>8.3f}")

    # Ratios
    if "Yukawa (tree boson)" in row and "Fermion loop" in row:
        yuk = row["Yukawa (tree boson)"]
        fer = row["Fermion loop"]
        ratio_R = fer["R_rms"] / yuk["R_rms"]
        ratio_r2 = fer["r2"] / yuk["r2"]
        ratio_q = fer["q_1pct"] / yuk["q_1pct"]
        print(f"\n  Ratios (fermion / Yukawa):")
        print(f"    R_rms:  {ratio_R:.4f}  (fermion is {1/ratio_R:.1f}x smaller)")
        print(f"    <r^2>:  {ratio_r2:.4e}")
        print(f"    q_1%:   {ratio_q:.2f}  (need {ratio_q:.1f}x higher q to resolve)")

        if "Scalar loop" in row:
            scl = row["Scalar loop"]
            ratio_R_sf = fer["R_rms"] / scl["R_rms"]
            print(f"    R_fer/R_scalar: {ratio_R_sf:.4f}  "
                  f"(parity barrier gives {1/ratio_R_sf:.1f}x extra)")

        if E_target == -0.05:  # reference point for physical units
            checks["fermion_smaller"] = ratio_R < 1.0
            checks["significant_suppression"] = ratio_r2 < 0.5
            checks["harder_to_resolve"] = ratio_q > 1.0

# ══════════════════════════════════════════════════════════════════════
# PHYSICAL UNITS (calibrated to pion)
# ══════════════════════════════════════════════════════════════════════

print("\n" + "=" * 70)
print("Physical units (calibrated to pion)")
print("=" * 70)

# Use E = -0.05 as reference
E_ref = -0.05
lam_yuk = find_lambda(V_yuk, E_ref)
lam_fer = find_lambda(V_fer, E_ref)
lam_scl = find_lambda(V_scl, E_ref)

if lam_yuk is not None and lam_fer is not None:
    alpha_yuk, _ = opt_alpha_energy(V_yuk, lam_yuk)
    alpha_fer, _ = opt_alpha_energy(V_fer, lam_fer)
    R_yuk = np.sqrt(3.0) / alpha_yuk
    R_fer = np.sqrt(3.0) / alpha_fer

    # Calibration: R_yuk (natural) → r_pi (physical)
    # r = R_nat * (hbar_c / m_f_phys)
    # r_pi = R_yuk * hbar_c / m_f_phys
    # → m_f_phys = R_yuk * hbar_c / r_pi
    m_f_phys = R_yuk * hbar_c / r_pi

    r_fer_phys = R_fer * hbar_c / m_f_phys   # fm
    r2_fer_phys = r_fer_phys**2

    if lam_scl is not None:
        alpha_scl, _ = opt_alpha_energy(V_scl, lam_scl)
        R_scl = np.sqrt(3.0) / alpha_scl
        r_scl_phys = R_scl * hbar_c / m_f_phys

    print(f"\n  Calibration: Yukawa composite = pion")
    print(f"    R_rms(Yukawa) = {R_yuk:.4f} (natural)  →  r_pi = {r_pi} fm")
    print(f"    Implied mediator mass: m_f = {m_f_phys:.1f} MeV")

    print(f"\n  Fermion composite (two bosons + fermion exchange):")
    print(f"    R_rms = {R_fer:.4f} (natural)  →  r = {r_fer_phys:.4f} fm")
    print(f"    <r^2> = {r2_fer_phys:.2e} fm^2")

    if lam_scl is not None:
        print(f"\n  Scalar-loop composite:")
        print(f"    R_rms = {R_scl:.4f} (natural)  →  r = {r_scl_phys:.4f} fm")

    print(f"\n  Experimental limit:")
    print(f"    Lambda > {Lambda_mu/1000:.0f} TeV  =>  <r^2> < {r2_mu_limit:.2e} fm^2")

    if r2_fer_phys < r2_mu_limit:
        factor = r2_mu_limit / r2_fer_phys
        print(f"\n  >>> BELOW experimental limit by factor {factor:.1f}")
        print(f"  >>> Fermionic composite IS consistent with 'pointlike'")
        checks["below_exp_limit"] = True
    else:
        factor = r2_fer_phys / r2_mu_limit
        print(f"\n  >>> ABOVE experimental limit by factor {factor:.1f}")
        print(f"  >>> Would be DETECTABLE — but see mediator mass scaling below")
        checks["below_exp_limit"] = False

    # Form factor resolution
    q_1_yuk = alpha_yuk * np.sqrt(4 * (1.0/np.sqrt(0.99) - 1))
    q_1_fer = alpha_fer * np.sqrt(4 * (1.0/np.sqrt(0.99) - 1))
    q_yuk_MeV = q_1_yuk * m_f_phys
    q_fer_MeV = q_1_fer * m_f_phys

    print(f"\n  Form factor 1% deviation scale:")
    print(f"    Yukawa:  q = {q_yuk_MeV:.0f} MeV")
    print(f"    Fermion: q = {q_fer_MeV:.0f} MeV")
    print(f"    LEP max: q ~ 100000 MeV")

    if q_fer_MeV > 100000:
        print(f"    >>> Fermion composite unresolvable at LEP")
        checks["unresolvable_LEP"] = True
    else:
        print(f"    >>> Fermion composite resolvable at LEP "
              f"(factor {100000/q_fer_MeV:.1f}x margin)")
        checks["unresolvable_LEP"] = False

    # Minimum mediator mass for undetectability
    # r2_phys(m_f) = r2_fer_phys * (m_f_phys/m_f)^2
    # r2_phys < r2_limit => m_f > m_f_phys * sqrt(r2_fer_phys/r2_limit)
    m_f_min = m_f_phys * np.sqrt(r2_fer_phys / r2_mu_limit)
    print(f"\n  Minimum mediator mass for undetectability:")
    print(f"    m_f > {m_f_min:.0f} MeV  ({m_f_min/1000:.1f} GeV)")

    # What if mediator is at electroweak scale?
    m_f_EW = 100000.0  # 100 GeV
    r2_EW = r2_fer_phys * (m_f_phys / m_f_EW)**2
    r_EW = np.sqrt(r2_EW)
    print(f"\n  At electroweak scale (m_f = 100 GeV):")
    print(f"    <r^2> = {r2_EW:.2e} fm^2")
    print(f"    r     = {r_EW:.2e} fm = {r_EW*1e3:.2e} am")
    print(f"    Ratio to limit: {r2_EW/r2_mu_limit:.2e}")

    checks["EW_below_limit"] = r2_EW < r2_mu_limit

# ══════════════════════════════════════════════════════════════════════
# SUMMARY
# ══════════════════════════════════════════════════════════════════════

print("\n" + "=" * 70)
print("Summary of checks:")
for name, passed in checks.items():
    status = "PASS" if passed else "FAIL"
    print(f"  {name}: {status}")

all_pass = all(checks.values()) if checks else False
print(f"\nall_checks_pass = {all_pass}")
print("=" * 70)

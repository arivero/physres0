"""
Fermionic composite form factor suppression — numerical checks.

Verifies:
1. Spectral function threshold exponents:
   - scalar coupling (3P0, L=1): alpha = 3/2
   - pseudoscalar coupling (1S0, L=0): alpha = 1/2
   - scalar loop comparison: alpha = 1/2
2. Position-space tail from numerical Laplace transform
3. Bound-state charge radius comparison at matched binding energy

See: fermion/2026-02-13-fermionic-composite-form-factor-suppression.md
"""

import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq

# ── Physical parameters (natural units, m_f = 1) ─────────────────────

m_f = 1.0
g = 1.0
threshold = 4 * m_f**2

checks = {}

print("=" * 70)
print("Fermionic Composite Form Factor Suppression — Numerical Checks")
print("=" * 70)

# ═══════════════════════════════════════════════════════════════════════
# PART 1: Spectral function threshold exponents
# ═══════════════════════════════════════════════════════════════════════

print("\n[Part 1] Spectral function threshold behavior")


def rho_fermion(s):
    """Im Pi for fermion loop: ~ (s - 4m^2)^{3/2} / s^{1/2}."""
    if s <= threshold:
        return 0.0
    delta = s - threshold
    return (g**2 / (24 * np.pi)) * delta**1.5 / np.sqrt(s)


def rho_fermion_ps(s):
    """Im Pi for fermion loop with PSEUDOSCALAR coupling (1S0, L=0).
    Tr[gamma5(k+m)gamma5(k+q+m)] = 4[-k.(k+q) + m^2]
    Integrand [m^2 + x(1-x)s] does NOT vanish at threshold.
    Result: ~ (s - 4m^2)^{1/2} (same as scalar loop — S-wave)."""
    if s <= threshold:
        return 0.0
    beta = np.sqrt(1 - threshold / s)
    # The integral gives beta * (s + 2m^2) / (6s), leading to beta ~ delta^{1/2}
    return (g**2 / (4 * np.pi)) * beta * (s + 2 * m_f**2) / (6 * s)


def rho_scalar(s):
    """Im Pi for scalar loop: ~ (s - 4m^2)^{1/2}."""
    if s <= threshold:
        return 0.0
    delta = s - threshold
    return (g**2 / (16 * np.pi)) * np.sqrt(delta / s)


# Verify exponents by log-log fit near threshold
deltas = np.logspace(-6, -1, 100)
s_vals = threshold + deltas

rho_F_vals = np.array([rho_fermion(s) for s in s_vals])
rho_PS_vals = np.array([rho_fermion_ps(s) for s in s_vals])
rho_S_vals = np.array([rho_scalar(s) for s in s_vals])

# Fit log(rho) = alpha * log(delta) + const
mask_F = rho_F_vals > 0
mask_PS = rho_PS_vals > 0
mask_S = rho_S_vals > 0

alpha_F = np.polyfit(np.log(deltas[mask_F]), np.log(rho_F_vals[mask_F]), 1)[0]
alpha_PS = np.polyfit(np.log(deltas[mask_PS]), np.log(rho_PS_vals[mask_PS]), 1)[0]
alpha_S = np.polyfit(np.log(deltas[mask_S]), np.log(rho_S_vals[mask_S]), 1)[0]

print(f"  Fermion scalar coupling (3P0): rho ~ delta^{alpha_F:.4f} (expected 1.5)")
print(f"  Fermion pseudoscalar   (1S0):  rho ~ delta^{alpha_PS:.4f} (expected 0.5)")
print(f"  Scalar loop:                   rho ~ delta^{alpha_S:.4f} (expected 0.5)")

checks["fermion_scalar_exponent"] = abs(alpha_F - 1.5) < 0.01
checks["fermion_ps_exponent"] = abs(alpha_PS - 0.5) < 0.01
checks["scalar_exponent"] = abs(alpha_S - 0.5) < 0.01
checks["parity_forced_barrier"] = alpha_F > alpha_PS + 0.5  # scalar coupling has extra barrier
checks["ps_matches_scalar_loop"] = abs(alpha_PS - alpha_S) < 0.05  # both S-wave

# ═══════════════════════════════════════════════════════════════════════
# PART 2: Position-space tail from spectral integral
# ═══════════════════════════════════════════════════════════════════════

print("\n[Part 2] Position-space tail V(r)")


def V_from_spectral(r, rho_func, s_max=200.0):
    """V(r) = -1/(4 pi r) * integral rho(s) * exp(-sqrt(s)*r) ds/(2pi)."""
    def integrand(s):
        return rho_func(s) * np.exp(-np.sqrt(s) * r)

    result, _ = quad(integrand, threshold + 1e-10, s_max,
                     limit=200, epsrel=1e-10)
    return -result / (4 * np.pi * r * 2 * np.pi)


# Compute V(r) at several r values
r_values = np.array([0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 4.0, 5.0])

V_F = np.array([V_from_spectral(r, rho_fermion) for r in r_values])
V_PS = np.array([V_from_spectral(r, rho_fermion_ps) for r in r_values])
V_S = np.array([V_from_spectral(r, rho_scalar) for r in r_values])

print(f"\n  {'r':>5}  {'V_scalar_cpg':>14}  {'V_pseudo_cpg':>14}  {'V_scalar_loop':>14}")
print("  " + "-" * 55)
for i, r in enumerate(r_values):
    print(f"  {r:>5.1f}  {V_F[i]:>14.6e}  {V_PS[i]:>14.6e}  {V_S[i]:>14.6e}")

# Verify tail exponent by fitting V(r) * r * exp(2m*r) ~ 1/r^{alpha+1}
r_fit = r_values[r_values >= 1.5]
V_F_fit = np.array([V_from_spectral(r, rho_fermion) for r in r_fit])
V_PS_fit = np.array([V_from_spectral(r, rho_fermion_ps) for r in r_fit])
V_S_fit = np.array([V_from_spectral(r, rho_scalar) for r in r_fit])

# Remove the exponential: multiply by exp(2m*r)
y_F = np.log(np.abs(V_F_fit) * r_fit * np.exp(2 * m_f * r_fit))
y_PS = np.log(np.abs(V_PS_fit) * r_fit * np.exp(2 * m_f * r_fit))
y_S = np.log(np.abs(V_S_fit) * r_fit * np.exp(2 * m_f * r_fit))

slope_F = np.polyfit(np.log(r_fit), y_F, 1)[0]
slope_PS = np.polyfit(np.log(r_fit), y_PS, 1)[0]
slope_S = np.polyfit(np.log(r_fit), y_S, 1)[0]

# V ~ exp(-2mr) / r^p  => |V| r exp(2mr) ~ 1/r^{p-1}
p_F = -slope_F + 1
p_PS = -slope_PS + 1
p_S = -slope_S + 1

print(f"\n  Position-space power law (V ~ exp(-2mr) / r^p):")
print(f"    Fermion scalar cpg (3P0):   p = {p_F:.3f} (expected 7/2 = 3.500)")
print(f"    Fermion pseudo cpg (1S0):   p = {p_PS:.3f} (expected 5/2 = 2.500)")
print(f"    Scalar loop:                p = {p_S:.3f} (expected 5/2 = 2.500)")

checks["fermion_tail_power"] = abs(p_F - 3.5) < 0.3
checks["pseudo_tail_power"] = abs(p_PS - 2.5) < 0.3
checks["scalar_tail_power"] = abs(p_S - 2.5) < 0.3
checks["parity_barrier_in_tail"] = p_F > p_PS + 0.5  # scalar cpg steeper than pseudo

# ═══════════════════════════════════════════════════════════════════════
# PART 3: Bound state comparison (Numerov, lean grid)
# ═══════════════════════════════════════════════════════════════════════

print("\n[Part 3] Bound-state charge radius comparison")

r0 = 1e-3
r_max_bs = 30.0
N = 4000
r_grid = np.linspace(r0, r_max_bs, N)
dr = r_grid[1] - r_grid[0]
M_red = 1.0  # reduced mass


def make_potential(lam, p_exp, mu_val):
    """V(r) = -lam * exp(-mu*r) / r^p, clamped at r0."""
    r_eff = np.maximum(r_grid, r0)
    return -lam * np.exp(-mu_val * r_eff) / r_eff**p_exp


def numerov(E, V_arr):
    """Numerov integration, returns u(r_grid)."""
    f = 2.0 * M_red * (V_arr - E)
    u = np.zeros(N)
    u[0] = 0.0
    u[1] = dr
    h2 = dr * dr
    for i in range(1, N - 1):
        u[i + 1] = (2 * (1 - 5 * h2 * f[i] / 12) * u[i]
                     - (1 + h2 * f[i - 1] / 12) * u[i - 1]) / \
                    (1 + h2 * f[i + 1] / 12)
    return u


def find_energy(V_arr, E_lo=-5.0, E_hi=-1e-6, n_scan=300):
    """Find ground-state energy by bisection on u(r_max)."""
    def tail(E):
        return numerov(E, V_arr)[-1]
    E_scan = np.linspace(E_lo, E_hi, n_scan)
    tails = [tail(E) for E in E_scan]
    for i in range(len(tails) - 1):
        if tails[i] * tails[i + 1] < 0:
            return brentq(tail, E_scan[i], E_scan[i + 1], xtol=1e-12)
    return None


def tune_coupling(p_exp, mu_val, E_target, lam_range=(1e-4, 1e4)):
    """Find coupling giving E = E_target."""
    def err(log_lam):
        lam = np.exp(log_lam)
        V = make_potential(lam, p_exp, mu_val)
        E = find_energy(V, E_lo=5 * E_target)
        if E is None:
            return -1.0
        return E - E_target
    log_lo, log_hi = np.log(lam_range[0]), np.log(lam_range[1])
    log_scan = np.linspace(log_lo, log_hi, 60)
    errs = [err(ll) for ll in log_scan]
    for i in range(len(errs) - 1):
        if errs[i] * errs[i + 1] < 0:
            return np.exp(brentq(err, log_scan[i], log_scan[i + 1],
                                 xtol=1e-8))
    return None


E_target = -0.1
mu_val = 2 * m_f

# Scan power-law exponents: p = 1 (Yukawa-like), 5/2 (scalar loop), 7/2 (fermion loop)
power_cases = [
    (1.0, "Yukawa (tree boson)"),
    (2.5, "Scalar loop tail"),
    (3.5, "Fermion loop tail"),
]

bs_results = {}

print(f"  Target binding energy: E = {E_target}")
print(f"  Exponential range: mu = {mu_val}")
print(f"\n  {'p':>5}  {'Label':>22}  {'lambda':>12}  {'E':>12}  {'<r^2>':>12}  {'R_rms':>10}")
print("  " + "-" * 80)

for p_exp, label in power_cases:
    lam = tune_coupling(p_exp, mu_val, E_target)
    if lam is None:
        print(f"  {p_exp:>5.1f}  {label:>22}  {'no binding':>12}")
        continue

    V = make_potential(lam, p_exp, mu_val)
    E = find_energy(V, E_lo=5 * E_target)
    if E is None:
        print(f"  {p_exp:>5.1f}  {label:>22}  {lam:>12.4e}  {'no state':>12}")
        continue

    u = numerov(E, V)
    norm2 = np.trapezoid(u**2, r_grid)
    u_n = u / np.sqrt(norm2)
    psi = u_n / r_grid

    r2 = np.trapezoid(r_grid**2 * psi**2 * r_grid**2, r_grid)
    R = np.sqrt(r2)
    bs_results[p_exp] = {"lam": lam, "E": E, "r2": r2, "R": R, "psi": psi}
    print(f"  {p_exp:>5.1f}  {label:>22}  {lam:>12.4e}  {E:>12.6e}  {r2:>12.6e}  {R:>10.6f}")

# Check monotonic shrinking
if len(bs_results) >= 2:
    ps = sorted(bs_results.keys())
    Rs = [bs_results[p]["R"] for p in ps]
    monotone = all(Rs[i] > Rs[i + 1] for i in range(len(Rs) - 1))
    print(f"\n  Radii monotonically decrease with power: {monotone}")
    checks["bs_monotone"] = monotone

    if 1.0 in bs_results and 3.5 in bs_results:
        ratio = bs_results[3.5]["R"] / bs_results[1.0]["R"]
        print(f"  R(fermion) / R(Yukawa) = {ratio:.4f}")
        print(f"  Fermionic composite is {1/ratio:.1f}x smaller at same binding energy")
        checks["bs_suppression"] = ratio < 0.7  # expect significant shrinking

# ═══════════════════════════════════════════════════════════════════════
# PART 4: Form factor comparison at matched binding energy
# ═══════════════════════════════════════════════════════════════════════

if 1.0 in bs_results and 3.5 in bs_results:
    print("\n[Part 4] Form factor F1(q^2) at matched binding energy")

    q_vals = np.linspace(0, 30.0, 300)

    def form_factor(psi_arr, q_vals):
        rho = np.abs(psi_arr)**2 * r_grid**2
        F1 = np.zeros_like(q_vals)
        for i, q in enumerate(q_vals):
            if q < 1e-15:
                F1[i] = np.trapezoid(rho, r_grid)
            else:
                j0 = np.sin(q * r_grid) / (q * r_grid)
                F1[i] = np.trapezoid(j0 * rho, r_grid)
        return F1 / F1[0]  # normalize F1(0) = 1

    F1_yuk = form_factor(bs_results[1.0]["psi"], q_vals)
    F1_fer = form_factor(bs_results[3.5]["psi"], q_vals)

    # Find 1% deviation scale
    def find_1pct(F1):
        dev = np.abs(F1 - 1.0)
        idx = np.argmax(dev > 0.01)
        return q_vals[idx] if dev[idx] > 0.01 else np.inf

    q1_yuk = find_1pct(F1_yuk)
    q1_fer = find_1pct(F1_fer)

    print(f"  Yukawa:   F1 deviates 1% at q = {q1_yuk:.3f}")
    print(f"  Fermion:  F1 deviates 1% at q = {q1_fer:.3f}")
    if q1_yuk > 0 and q1_fer < np.inf:
        ratio = q1_fer / q1_yuk
        print(f"  Ratio: {ratio:.2f}x (need {ratio:.1f}x higher q to resolve fermion composite)")
        checks["ff_harder_to_resolve"] = ratio > 1.5
    elif q1_fer == np.inf:
        print(f"  Fermion composite unresolvable in scanned range!")
        checks["ff_harder_to_resolve"] = True

    # Slopes
    slope_yuk = -bs_results[1.0]["r2"] / 6.0
    slope_fer = -bs_results[3.5]["r2"] / 6.0
    sr = abs(slope_fer / slope_yuk)
    print(f"\n  dF1/d(q^2)|_0:  Yukawa = {slope_yuk:.4e},  Fermion = {slope_fer:.4e}")
    print(f"  Slope ratio: {sr:.4e} (fermion {1/sr:.0f}x flatter)")
    checks["slope_suppressed"] = sr < 0.5

# ═══════════════════════════════════════════════════════════════════════
# Summary
# ═══════════════════════════════════════════════════════════════════════

print("\n" + "=" * 70)
print("Summary:")
for name, passed in checks.items():
    status = "PASS" if passed else "FAIL"
    print(f"  {name}: {status}")

all_checks_pass = all(checks.values())
print(f"\nall_checks_pass = {all_checks_pass}")
print("=" * 70)

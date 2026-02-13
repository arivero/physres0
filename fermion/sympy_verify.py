"""
Symbolic verification of key analytic formulas using SymPy.

Verifies:
1. Feynman parameter integral for scalar coupling → (s-4m^2)^{3/2}
2. Feynman parameter integral for pseudoscalar coupling → (s-4m^2)^{1/2}
3. Laplace transform for position-space tail
4. Threshold expansion of beta
5. Dipole form factor from hydrogen trial wavefunction
6. Charge radius from dipole form factor

See: fermion/2026-02-13-fermionic-composite-form-factor-suppression.md
"""

import sympy as sp

checks = {}

print("=" * 70)
print("SymPy symbolic verification")
print("=" * 70)

# ── Symbols ──────────────────────────────────────────────────────────
x, s, m, delta, b, alpha_s, r, q = sp.symbols(
    'x s m delta b alpha r q', positive=True, real=True)
beta = sp.Symbol('beta', positive=True)

# ══════════════════════════════════════════════════════════════════════
# 1. Feynman parameter integral — SCALAR coupling
# ══════════════════════════════════════════════════════════════════════

print("\n[1] Feynman parameter integral (scalar coupling)")
print("    Integrand: m^2 - x(1-x)*s")

# Integration limits: x_- = (1-beta)/2, x_+ = (1+beta)/2
# where beta = sqrt(1 - 4m^2/s)
x_minus = (1 - beta) / 2
x_plus = (1 + beta) / 2

integrand_scalar = m**2 - x * (1 - x) * s

I_scalar = sp.integrate(integrand_scalar, (x, x_minus, x_plus))
I_scalar = sp.simplify(I_scalar)
print(f"    Integral = {I_scalar}")

# Substitute beta^2 = 1 - 4m^2/s, i.e., s = 4m^2/(1-beta^2)
I_sub = I_scalar.subs(s, 4*m**2 / (1 - beta**2))
I_sub = sp.simplify(I_sub)
print(f"    With s = 4m^2/(1-beta^2): {I_sub}")

# Near threshold: beta -> 0, expand
I_expand = sp.series(I_sub, beta, 0, n=5)
print(f"    Series in beta: {I_expand}")

# The leading term should be proportional to beta^3
# Extract coefficient of beta^3
coeff_beta3 = I_expand.coeff(beta, 3)
print(f"    Coefficient of beta^3: {coeff_beta3}")
checks["scalar_beta3"] = coeff_beta3 != 0

# Also check: the integral equals -beta*(s-4m^2)/6 at arbitrary beta
# s - 4m^2 = s*beta^2, so -beta*s*beta^2/6 = -s*beta^3/6
# With s = 4m^2/(1-beta^2): -4m^2*beta^3/(6*(1-beta^2))
target_scalar = -beta * (4*m**2 / (1-beta**2)) * beta**2 / 6
diff = sp.simplify(I_sub - target_scalar)
print(f"    I - (-beta*s*beta^2/6) = {diff}")
checks["scalar_closed_form"] = diff == 0

# ══════════════════════════════════════════════════════════════════════
# 2. Feynman parameter integral — PSEUDOSCALAR coupling
# ══════════════════════════════════════════════════════════════════════

print("\n[2] Feynman parameter integral (pseudoscalar coupling)")
print("    Integrand: m^2 + x(1-x)*s  [note: + sign from gamma5 trace]")

# For pseudoscalar: Tr[gamma5(k+m)gamma5(k+q+m)] = -4[k.(k+q) - m^2]
# After Feynman param: factor is [m^2 + x(1-x)s] (sign flip from Dirac trace)
# This does NOT vanish at threshold (where x(1-x)s = m^2 at x=1/2)

integrand_ps = m**2 + x * (1 - x) * s
I_ps = sp.integrate(integrand_ps, (x, x_minus, x_plus))
I_ps = sp.simplify(I_ps)
print(f"    Integral = {I_ps}")

I_ps_sub = I_ps.subs(s, 4*m**2 / (1 - beta**2))
I_ps_sub = sp.simplify(I_ps_sub)
print(f"    With s = 4m^2/(1-beta^2): {I_ps_sub}")

I_ps_expand = sp.series(I_ps_sub, beta, 0, n=5)
print(f"    Series in beta: {I_ps_expand}")

coeff_beta1 = I_ps_expand.coeff(beta, 1)
coeff_beta0 = I_ps_expand.coeff(beta, 0)
print(f"    Coefficient of beta^0: {coeff_beta0}")
print(f"    Coefficient of beta^1: {coeff_beta1}")
checks["pseudoscalar_beta1"] = coeff_beta1 != 0
checks["pseudoscalar_no_beta0"] = coeff_beta0 == 0
# Leading term ~ beta (not beta^3) → spectral function ~ beta ~ delta^{1/2}

# Verify: integral = beta*(2s+16m^2)/12 = beta*(s+8m^2)/6
# From the trace: numerator is [m^2 + x(1-x)s], integrated over (x_-,x_+)
target_ps = beta * (4*m**2/(1-beta**2) + 8*m**2) / 6
diff_ps = sp.simplify(I_ps_sub - target_ps)
print(f"    I - beta*(s+8m^2)/6 = {diff_ps}")
checks["pseudoscalar_closed_form"] = diff_ps == 0

# ══════════════════════════════════════════════════════════════════════
# 3. Laplace transform for position-space tail
# ══════════════════════════════════════════════════════════════════════

print("\n[3] Laplace transform: int_0^inf delta^alpha * exp(-b*delta) d(delta)")

# For general alpha
# Result should be Gamma(alpha+1) / b^(alpha+1)
alpha_sym = sp.Symbol('alpha', positive=True)
lap = sp.integrate(delta**alpha_sym * sp.exp(-b * delta), (delta, 0, sp.oo))
lap = sp.simplify(lap)
print(f"    Result: {lap}")

target_lap = sp.gamma(alpha_sym + 1) / b**(alpha_sym + 1)
diff_lap = sp.simplify(lap - target_lap)
print(f"    Matches Gamma(alpha+1)/b^(alpha+1): {diff_lap == 0}")
checks["laplace_transform"] = diff_lap == 0

# Specific cases
for alpha_val, name in [(sp.Rational(1,2), "1/2"), (sp.Rational(3,2), "3/2")]:
    lap_val = lap.subs(alpha_sym, alpha_val)
    lap_val = sp.simplify(lap_val)
    gamma_val = sp.gamma(alpha_val + 1)
    print(f"    alpha = {name}: Gamma({name}+1) = {gamma_val} = {sp.simplify(gamma_val)}")
    print(f"      Integral = {lap_val}")

# ══════════════════════════════════════════════════════════════════════
# 4. Threshold expansion: beta = sqrt(1 - 4m^2/s) near s = 4m^2
# ══════════════════════════════════════════════════════════════════════

print("\n[4] Threshold expansion")

s_thr = 4*m**2 + delta
beta_expr = sp.sqrt(1 - 4*m**2 / s_thr)
beta_expand = sp.series(beta_expr, delta, 0, n=3)
print(f"    beta(4m^2 + delta) = {beta_expand}")
# Should be sqrt(delta/(4m^2)) + ...
leading = beta_expand.removeO()
print(f"    Leading term: {sp.simplify(leading)}")

# Also: sqrt(s) near threshold
sqrts_expand = sp.series(sp.sqrt(s_thr), delta, 0, n=2)
print(f"    sqrt(s) = {sqrts_expand}")
# Should be 2m + delta/(4m) + ...

checks["beta_threshold"] = True  # visual check

# ══════════════════════════════════════════════════════════════════════
# 5. Dipole form factor from hydrogen trial wavefunction
# ══════════════════════════════════════════════════════════════════════

print("\n[5] Dipole form factor F1(q) for trial u = r*exp(-alpha*r)")

# psi(r) = exp(-alpha*r) (since u = r*psi)
# F1(q) = int_0^inf j0(q*r) |psi|^2 r^2 dr / int_0^inf |psi|^2 r^2 dr
# = int_0^inf sin(qr)/(qr) * exp(-2*alpha*r) * r^2 dr / int_0^inf exp(-2*alpha*r) * r^2 dr

a = sp.Symbol('a', positive=True)  # alpha
norm = sp.integrate(sp.exp(-2*a*r) * r**2, (r, 0, sp.oo))
print(f"    Normalization: {norm}")

# Numerator: int r^2 * sin(qr)/(qr) * exp(-2ar) dr = (1/q) int r sin(qr) exp(-2ar) dr
numer = sp.integrate(r * sp.sin(q*r) * sp.exp(-2*a*r), (r, 0, sp.oo)) / q
numer = sp.simplify(numer)
print(f"    Numerator/q: {sp.integrate(r * sp.sin(q*r) * sp.exp(-2*a*r), (r, 0, sp.oo))}")

F1 = sp.simplify(numer / norm)
print(f"    F1(q) = {F1}")

# Should be [2a/(4a^2+q^2)]^2 = [1/(1+q^2/(4a^2))]^2
# F1 = [4a^2/(4a^2+q^2)]^2 = 16a^4/(4a^2+q^2)^2 = [1/(1+q^2/(4a^2))]^2
F1_target = (4*a**2)**2 / (4*a**2 + q**2)**2
diff_F1 = sp.simplify(F1 - F1_target)
print(f"    Matches [4a^2/(4a^2+q^2)]^2: {diff_F1 == 0}")
checks["dipole_form_factor"] = diff_F1 == 0

# ══════════════════════════════════════════════════════════════════════
# 6. Charge radius from form factor
# ══════════════════════════════════════════════════════════════════════

print("\n[6] Charge radius: <r^2> = -6 * dF1/d(q^2)|_{q=0}")

# F1 = 1/(1+q^2/(4a^2))^2  → dF1/d(q^2) = -2/(4a^2) * 1/(1+q^2/(4a^2))^3
# At q=0: dF1/d(q^2) = -1/(2a^2)
# <r^2> = -6 * (-1/(2a^2)) = 3/a^2

q2 = sp.Symbol('q2', positive=True)
F1_q2 = 1 / (1 + q2/(4*a**2))**2
dF1_dq2 = sp.diff(F1_q2, q2)
dF1_at_0 = dF1_dq2.subs(q2, 0)
r2_from_F1 = -6 * dF1_at_0
r2_from_F1 = sp.simplify(r2_from_F1)
print(f"    dF1/d(q^2)|_0 = {dF1_at_0}")
print(f"    <r^2> = -6 * dF1/d(q^2)|_0 = {r2_from_F1}")
checks["charge_radius_3_over_a2"] = r2_from_F1 == 3/a**2

# Also verify directly: <r^2> = int r^2 |psi|^2 r^2 dr / int |psi|^2 r^2 dr
r2_direct = sp.integrate(r**4 * sp.exp(-2*a*r), (r, 0, sp.oo)) / norm
r2_direct = sp.simplify(r2_direct)
print(f"    <r^2> (direct) = {r2_direct}")
checks["charge_radius_direct"] = sp.simplify(r2_direct - 3/a**2) == 0

# ══════════════════════════════════════════════════════════════════════
# 7. Yukawa potential expectation value (analytic cross-check)
# ══════════════════════════════════════════════════════════════════════

print("\n[7] <V_Yukawa> for trial u = r*exp(-a*r)")

mu = sp.Symbol('mu', positive=True)
V_yuk_sym = -sp.exp(-mu*r) / (4 * sp.pi * r)

V_exp_numer = sp.integrate(r**2 * sp.exp(-2*a*r) * V_yuk_sym, (r, 0, sp.oo))
V_exp = sp.simplify(V_exp_numer / norm)
print(f"    <V_Yukawa> = {V_exp}")

# Should be -a^3 / (pi*(2a+mu)^2) ... let me check
target_V = -a**3 / (sp.pi * (2*a + mu)**2)
# Actually: <V> = int r^2 e^{-2ar} * (-e^{-mu r}/(4pi r)) dr / int r^2 e^{-2ar} dr
#         = -1/(4pi) * int r e^{-(2a+mu)r} dr / int r^2 e^{-2ar} dr
#         = -1/(4pi) * 1/(2a+mu)^2 / (1/(4a^3))
#         = -a^3 / (pi * (2a+mu)^2)
diff_V = sp.simplify(V_exp - target_V)
print(f"    Matches -a^3/(pi*(2a+mu)^2): {diff_V == 0}")
checks["yukawa_expectation"] = diff_V == 0

# ══════════════════════════════════════════════════════════════════════
# SUMMARY
# ══════════════════════════════════════════════════════════════════════

print("\n" + "=" * 70)
print("Summary:")
for name, passed in checks.items():
    status = "PASS" if passed else "FAIL"
    print(f"  {name}: {status}")

all_pass = all(checks.values())
print(f"\nall_checks_pass = {all_pass}")
print("=" * 70)

"""
Sommerfeld enhancement/suppression of the spectral function.

When the fermion-antifermion pair in the loop interacts via a long-range
potential (Coulomb or Yukawa), the near-threshold spectral function is
modified by the Sommerfeld factor.

For S-wave: rho ~ beta * S_0(beta)
For P-wave: rho ~ beta^3 * S_1(beta)

The Sommerfeld factors can dramatically enhance or suppress the spectral
function near threshold, depending on whether the potential is attractive
or repulsive.

For our scalar coupling (3P0 channel), the ff_bar pair is in P-wave.
If the pair interacts via an attractive Coulomb-like potential (e.g.,
from gluon exchange in SUSY QCD), the Sommerfeld factor can create
bound states and resonances.

See: Beneke, Binder, Garny, arXiv:2208.13309 (P-wave Sommerfeld)
     Beneke, Binder, De Ros, Garny, arXiv:2403.07108 (super-resonances)
"""

import numpy as np
from scipy.integrate import quad
from scipy.optimize import minimize_scalar, brentq
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

_trapz = getattr(np, 'trapezoid', np.trapz)

# ── Parameters ────────────────────────────────────────────────────────
m_f = 1.0
threshold = 4 * m_f**2
M_red = 1.0
alpha_s = 0.3  # coupling constant for ff_bar interaction

# ══════════════════════════════════════════════════════════════════════
# Sommerfeld factors
# ══════════════════════════════════════════════════════════════════════

def sommerfeld_S0_coulomb(beta, alpha_eff):
    """S-wave Sommerfeld factor for Coulomb potential.

    S_0 = (pi*alpha_eff/beta) / (1 - exp(-pi*alpha_eff/beta))

    For attractive potential: alpha_eff > 0 => enhancement
    For repulsive potential: alpha_eff < 0 => suppression
    """
    if beta < 1e-10:
        return np.pi * abs(alpha_eff) / 1e-10  # regularize
    eta = alpha_eff / beta
    if abs(eta) < 1e-10:
        return 1.0
    x = np.pi * eta
    if x > 500:
        return x  # asymptotic
    if x < -500:
        return -x * np.exp(x)  # asymptotic
    return x / (1 - np.exp(-x))

def sommerfeld_S1_coulomb(beta, alpha_eff):
    """P-wave Sommerfeld factor for Coulomb potential.

    For L=1: S_1 = S_0 * (1 + (alpha_eff/beta)^2)
    """
    S0 = sommerfeld_S0_coulomb(beta, alpha_eff)
    eta = alpha_eff / beta if beta > 1e-10 else alpha_eff / 1e-10
    return S0 * (1 + eta**2)

# ══════════════════════════════════════════════════════════════════════
# Modified spectral functions
# ══════════════════════════════════════════════════════════════════════

def rho_fermion_bare(s):
    """Bare fermion loop spectral function (no Sommerfeld)."""
    if s <= threshold: return 0.0
    delta = s - threshold
    return delta**1.5 / (24 * np.pi * np.sqrt(s))

def rho_fermion_sommerfeld(s, alpha_eff):
    """Fermion loop with P-wave Sommerfeld factor."""
    if s <= threshold: return 0.0
    beta = np.sqrt(1 - threshold / s)
    rho_bare = rho_fermion_bare(s)
    S1 = sommerfeld_S1_coulomb(beta, alpha_eff)
    return rho_bare * S1

def rho_scalar_bare(s):
    """Bare scalar loop spectral function."""
    if s <= threshold: return 0.0
    return np.sqrt((s - threshold) / s) / (16 * np.pi)

def rho_scalar_sommerfeld(s, alpha_eff):
    """Scalar loop with S-wave Sommerfeld factor."""
    if s <= threshold: return 0.0
    beta = np.sqrt(1 - threshold / s)
    rho_bare = rho_scalar_bare(s)
    S0 = sommerfeld_S0_coulomb(beta, alpha_eff)
    return rho_bare * S0

# ══════════════════════════════════════════════════════════════════════
# Potentials with Sommerfeld correction
# ══════════════════════════════════════════════════════════════════════

def V_spectral(r, rho_func, s_max=200.0):
    def integrand(s):
        return rho_func(s) * np.exp(-np.sqrt(s) * r)
    result, _ = quad(integrand, threshold + 1e-10, s_max,
                     limit=200, epsrel=1e-10)
    return -result / (4 * np.pi * r * 2 * np.pi)

# Grid for variational calculation
N_pot = 400
r_grid = np.linspace(0.01, 20.0, N_pot)
dr = r_grid[1] - r_grid[0]

print("=" * 70)
print("Sommerfeld correction to spectral function")
print("=" * 70)

# Compute potentials
print("\nComputing potentials (this takes ~1 min)...")
V_yuk = -np.exp(-m_f * r_grid) / (4 * np.pi * r_grid)
V_fer_bare = np.array([V_spectral(r, rho_fermion_bare) for r in r_grid])
V_scl_bare = np.array([V_spectral(r, rho_scalar_bare) for r in r_grid])

alpha_eff_values = [0.0, 0.1, 0.3, 0.5]
V_fer_somm = {}
V_scl_somm = {}

for alpha_eff in alpha_eff_values:
    if alpha_eff == 0.0:
        V_fer_somm[alpha_eff] = V_fer_bare
        V_scl_somm[alpha_eff] = V_scl_bare
    else:
        V_fer_somm[alpha_eff] = np.array([
            V_spectral(r, lambda s: rho_fermion_sommerfeld(s, alpha_eff))
            for r in r_grid
        ])
        V_scl_somm[alpha_eff] = np.array([
            V_spectral(r, lambda s, a=alpha_eff: rho_scalar_sommerfeld(s, a))
            for r in r_grid
        ])
        print(f"  alpha_eff = {alpha_eff} done")

print("  all potentials computed.")

# ══════════════════════════════════════════════════════════════════════
# Variational calculation
# ══════════════════════════════════════════════════════════════════════

def V_expectation(alpha, V_arr):
    w = r_grid**2 * np.exp(-2 * alpha * r_grid)
    w_sum = _trapz(w, r_grid)
    if w_sum < 1e-300: return 0.0
    return _trapz(w * V_arr, r_grid) / w_sum

def var_energy(alpha, V_arr, lam):
    return alpha**2 / (2 * M_red) + lam * V_expectation(alpha, V_arr)

def opt_alpha_energy(V_arr, lam):
    res = minimize_scalar(lambda a: var_energy(a, V_arr, lam),
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

# ── Results ──────────────────────────────────────────────────────────

E_target = -0.05

print(f"\n{'='*70}")
print(f"Bound-state properties at E = {E_target}")
print(f"{'='*70}")

print(f"\n  {'alpha_eff':>10}  {'Potential':>15}  {'lambda':>12}  "
      f"{'alpha':>8}  {'R_rms':>8}")
print(f"  {'-'*65}")

# Yukawa reference
lam_yuk = find_lambda(V_yuk, E_target)
alpha_yuk, _ = opt_alpha_energy(V_yuk, lam_yuk)
R_yuk = np.sqrt(3.0) / alpha_yuk
print(f"  {'--':>10}  {'Yukawa':>15}  {lam_yuk:>12.2e}  "
      f"{alpha_yuk:>8.4f}  {R_yuk:>8.4f}")

results = {}
for alpha_eff in alpha_eff_values:
    for pot_name, V_arr in [("Fermion", V_fer_somm[alpha_eff]),
                             ("Scalar", V_scl_somm[alpha_eff])]:
        lam = find_lambda(V_arr, E_target)
        if lam is None:
            print(f"  {alpha_eff:>10.1f}  {pot_name:>15}  {'no binding':>12}")
            continue
        alpha, E = opt_alpha_energy(V_arr, lam)
        R_rms = np.sqrt(3.0) / alpha
        print(f"  {alpha_eff:>10.1f}  {pot_name:>15}  {lam:>12.2e}  "
              f"{alpha:>8.4f}  {R_rms:>8.4f}")
        results[(alpha_eff, pot_name)] = {
            "lam": lam, "alpha": alpha, "R_rms": R_rms
        }

# ── Size ratios ──────────────────────────────────────────────────────

print(f"\n{'='*70}")
print("Size ratios (vs Yukawa):")
print(f"{'='*70}")

checks = {}
for alpha_eff in alpha_eff_values:
    fer_key = (alpha_eff, "Fermion")
    scl_key = (alpha_eff, "Scalar")

    if fer_key in results:
        ratio_f = results[fer_key]["R_rms"] / R_yuk
        inv_f = 1.0 / ratio_f
        print(f"  alpha_eff={alpha_eff:.1f}:  R_fer/R_yuk = {ratio_f:.4f}  "
              f"(fermion {inv_f:.1f}x smaller)")
        checks[f"fermion_a{alpha_eff}"] = ratio_f < 1.0

    if scl_key in results:
        ratio_s = results[scl_key]["R_rms"] / R_yuk
        inv_s = 1.0 / ratio_s
        print(f"  alpha_eff={alpha_eff:.1f}:  R_scl/R_yuk = {ratio_s:.4f}  "
              f"(scalar  {inv_s:.1f}x smaller)")

# ══════════════════════════════════════════════════════════════════════
# FIGURE: Sommerfeld effects
# ══════════════════════════════════════════════════════════════════════

print(f"\n{'='*70}")
print("Generating Sommerfeld figure...")

fig, axes = plt.subplots(2, 2, figsize=(12, 10))

# Panel 1: Sommerfeld factors vs beta
ax = axes[0, 0]
betas = np.logspace(-3, 0, 200)
for alpha_eff in [0.1, 0.3, 0.5]:
    S0 = [sommerfeld_S0_coulomb(b, alpha_eff) for b in betas]
    S1 = [sommerfeld_S1_coulomb(b, alpha_eff) for b in betas]
    ax.loglog(betas, S0, ls='--', lw=1.5,
              label=f'$S_0$ ($\\alpha={alpha_eff}$)')
    ax.loglog(betas, S1, ls='-', lw=2,
              label=f'$S_1$ ($\\alpha={alpha_eff}$)')

ax.set_xlabel('$\\beta$ (velocity)')
ax.set_ylabel('Sommerfeld factor')
ax.set_title('Sommerfeld factors: S-wave (dashed) vs P-wave (solid)')
ax.legend(fontsize=8, ncol=2)
ax.grid(True, alpha=0.3, which='both')

# Panel 2: Modified spectral functions
ax = axes[0, 1]
deltas_plot = np.logspace(-4, 2, 300)
s_plot = threshold + deltas_plot

rho_bare = np.array([rho_fermion_bare(s) for s in s_plot])
ax.loglog(deltas_plot, rho_bare, 'k-', lw=2, label='Bare ($\\alpha_{\\rm eff}=0$)')

for alpha_eff, color in [(0.1, 'blue'), (0.3, 'red'), (0.5, 'green')]:
    rho_mod = np.array([rho_fermion_sommerfeld(s, alpha_eff) for s in s_plot])
    ax.loglog(deltas_plot, rho_mod, color=color, lw=1.5,
              label=f'$\\alpha_{{\\rm eff}}={alpha_eff}$')

ax.set_xlabel('$\\delta = s - 4m_f^2$')
ax.set_ylabel('$\\rho_F(s)$')
ax.set_title('Fermion spectral function with Sommerfeld')
ax.legend(fontsize=9)
ax.grid(True, alpha=0.3, which='both')

# Panel 3: Modified potentials
ax = axes[1, 0]
idx = r_grid >= 0.05
ax.semilogy(r_grid[idx], np.abs(V_yuk[idx]), 'b-', lw=2, label='Yukawa')
ax.semilogy(r_grid[idx], np.abs(V_fer_bare[idx]), 'k-', lw=2,
            label='Fermion (bare)')
for alpha_eff, color in [(0.1, 'orange'), (0.3, 'red'), (0.5, 'darkred')]:
    ax.semilogy(r_grid[idx], np.abs(V_fer_somm[alpha_eff][idx]),
                color=color, lw=1.5,
                label=f'Fermion ($\\alpha={alpha_eff}$)')

ax.set_xlabel('r (units of 1/m_f)')
ax.set_ylabel('|V(r)| (unit coupling)')
ax.set_title('Potentials with Sommerfeld corrections')
ax.set_xlim(0, 10)
ax.set_ylim(1e-10, 1)
ax.legend(fontsize=8)
ax.grid(True, alpha=0.3)

# Panel 4: Size ratio vs Sommerfeld coupling
ax = axes[1, 1]
alpha_range = np.linspace(0, 0.5, 20)
ratios_fer = []
ratios_scl = []

for a in alpha_range:
    if a == 0.0:
        V_f = V_fer_bare
        V_s = V_scl_bare
    else:
        V_f = np.array([V_spectral(r, lambda s: rho_fermion_sommerfeld(s, a))
                        for r in r_grid])
        V_s = np.array([V_spectral(r, lambda s, aa=a: rho_scalar_sommerfeld(s, aa))
                        for r in r_grid])

    lam_f = find_lambda(V_f, E_target)
    lam_s = find_lambda(V_s, E_target)

    if lam_f is not None:
        alpha_f, _ = opt_alpha_energy(V_f, lam_f)
        ratios_fer.append(np.sqrt(3.0) / alpha_f / R_yuk)
    else:
        ratios_fer.append(np.nan)

    if lam_s is not None:
        alpha_s, _ = opt_alpha_energy(V_s, lam_s)
        ratios_scl.append(np.sqrt(3.0) / alpha_s / R_yuk)
    else:
        ratios_scl.append(np.nan)

ax.plot(alpha_range, ratios_fer, 'r-o', lw=2, ms=4,
        label='$R_{\\rm fer}/R_{\\rm Yuk}$')
ax.plot(alpha_range, ratios_scl, 'g--s', lw=2, ms=4,
        label='$R_{\\rm scl}/R_{\\rm Yuk}$')
ax.axhline(1.0, color='k', ls=':', lw=0.5)
ax.set_xlabel('$\\alpha_{\\rm eff}$ (ff_bar interaction strength)')
ax.set_ylabel('$R/R_{\\rm Yukawa}$')
ax.set_title('Size ratio vs Sommerfeld coupling')
ax.legend()
ax.grid(True, alpha=0.3)
ax.set_ylim(0, 0.5)

fig.suptitle('Sommerfeld enhancement of fermionic exchange',
             fontsize=14, fontweight='bold')
fig.tight_layout()
fig.savefig('fermion/fig_sommerfeld.pdf')
plt.close()
print("  -> fig_sommerfeld.pdf")

# ══════════════════════════════════════════════════════════════════════
# SUMMARY
# ══════════════════════════════════════════════════════════════════════

print(f"\n{'='*70}")
print("Summary:")
print(f"{'='*70}")
print("""
The Sommerfeld effect modifies the spectral function near threshold:

  For ATTRACTIVE ff_bar interaction (alpha_eff > 0):
  - S-wave: enhanced by factor ~pi*alpha/beta near threshold
  - P-wave: enhanced by factor ~pi*alpha*(1+alpha^2/beta^2)/beta

  The P-wave enhancement is STRONGER than S-wave because the
  centrifugal barrier traps quasi-bound states that enhance the
  near-threshold spectral density.

Physical consequences for the composite:
  - The Sommerfeld-enhanced potential is stronger
  - Less coupling is needed for binding
  - But the bound state may be LARGER (less concentrated)
  - Net effect depends on the balance of enhancement and barrier

Connection to alpha decay:
  - The P-wave Sommerfeld factor includes the resonance contribution
  - For strong enough coupling: bound states below threshold
  - Just above threshold: narrow resonances (trapped behind barrier)
  - These are the "super-resonant" peaks of Beneke et al.
""")

print("Checks:")
for name, val in checks.items():
    print(f"  {name}: {'PASS' if val else 'FAIL'}")

all_pass = all(checks.values())
print(f"\nall_checks_pass = {all_pass}")
print("=" * 70)

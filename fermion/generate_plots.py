"""
Generate publication-quality plots for the fermionic composite paper.

Produces:
  fig_potentials.pdf   — V(r) for Yukawa, scalar loop, fermion loop
  fig_formfactor.pdf   — F1(q^2) at matched binding energy
  fig_scaling.pdf      — R_rms vs mediator mass with experimental limit
  fig_spectral.pdf     — Spectral functions near threshold

See: fermion/paper.tex
"""

import numpy as np
from scipy.integrate import quad
from scipy.optimize import minimize_scalar, brentq
import matplotlib
matplotlib.use('Agg')  # non-interactive backend
import matplotlib.pyplot as plt
from matplotlib.ticker import LogLocator

# Style
plt.rcParams.update({
    'font.size': 11,
    'axes.labelsize': 13,
    'legend.fontsize': 10,
    'figure.figsize': (6, 4.5),
    'figure.dpi': 150,
    'savefig.bbox': 'tight',
    'savefig.pad_inches': 0.1,
})

# ── Parameters ────────────────────────────────────────────────────────
m_f = 1.0
threshold = 4 * m_f**2
M_red = 1.0
hbar_c = 197.3269804  # MeV fm
r_pi = 0.659          # fm

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

N_pot = 300
r_grid = np.linspace(0.01, 15.0, N_pot)

print("Computing potentials...")
V_yuk = -np.exp(-m_f * r_grid) / (4 * np.pi * r_grid)
V_fer = np.array([V_spectral(r, rho_fermion) for r in r_grid])
V_scl = np.array([V_spectral(r, rho_scalar) for r in r_grid])
print("  done.")

# ── Variational method ────────────────────────────────────────────────

def V_expectation(alpha, V_arr):
    w = r_grid**2 * np.exp(-2 * alpha * r_grid)
    w_sum = np.trapezoid(w, r_grid)
    if w_sum < 1e-300: return 0.0
    return np.trapezoid(w * V_arr, r_grid) / w_sum

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

# ══════════════════════════════════════════════════════════════════════
# FIGURE 1: Potentials
# ══════════════════════════════════════════════════════════════════════

print("Figure 1: Potentials")
fig, ax = plt.subplots()
r_plot = r_grid[r_grid >= 0.1]

# Scale loop potentials by coupling needed for binding at E=-0.05
lam_yuk = find_lambda(V_yuk, -0.05)
lam_fer = find_lambda(V_fer, -0.05)
lam_scl = find_lambda(V_scl, -0.05)

idx = r_grid >= 0.1
ax.semilogy(r_grid[idx], np.abs(lam_yuk * V_yuk[idx]),
            'b-', lw=2, label=f'Yukawa ($\\lambda={lam_yuk:.0f}$)')
ax.semilogy(r_grid[idx], np.abs(lam_scl * V_scl[idx]),
            'g--', lw=2, label=f'Scalar loop ($\\lambda={lam_scl:.0f}$)')
ax.semilogy(r_grid[idx], np.abs(lam_fer * V_fer[idx]),
            'r-.', lw=2, label=f'Fermion loop ($\\lambda={lam_fer:.1f}$)')

ax.set_xlabel('$r$ (units of $1/m_f$)')
ax.set_ylabel('$|V(r)|$')
ax.set_title('Binding potentials at matched $E = -0.05$')
ax.set_xlim(0.1, 10)
ax.set_ylim(1e-8, 10)
ax.legend()
ax.grid(True, alpha=0.3)
fig.savefig('fermion/fig_potentials.pdf')
plt.close()
print("  -> fig_potentials.pdf")

# ══════════════════════════════════════════════════════════════════════
# FIGURE 2: Form factors
# ══════════════════════════════════════════════════════════════════════

print("Figure 2: Form factors")
fig, ax = plt.subplots()

alpha_yuk, _ = opt_alpha_energy(V_yuk, lam_yuk)
alpha_fer, _ = opt_alpha_energy(V_fer, lam_fer)
alpha_scl, _ = opt_alpha_energy(V_scl, lam_scl)

q_vals = np.linspace(0, 3, 500)

def F1_dipole(q, alpha):
    return 1.0 / (1 + q**2 / (4 * alpha**2))**2

ax.plot(q_vals, F1_dipole(q_vals, alpha_yuk), 'b-', lw=2,
        label=f'Yukawa ($\\alpha={alpha_yuk:.2f}$)')
ax.plot(q_vals, F1_dipole(q_vals, alpha_scl), 'g--', lw=2,
        label=f'Scalar loop ($\\alpha={alpha_scl:.2f}$)')
ax.plot(q_vals, F1_dipole(q_vals, alpha_fer), 'r-.', lw=2,
        label=f'Fermion loop ($\\alpha={alpha_fer:.2f}$)')

ax.axhline(0.99, color='gray', ls=':', alpha=0.5, label='1% deviation')
ax.set_xlabel('$q$ (units of $m_f$)')
ax.set_ylabel('$F_1(q^2)$')
ax.set_title('Form factors at matched binding energy $E = -0.05$')
ax.set_ylim(0.5, 1.02)
ax.legend(loc='lower left')
ax.grid(True, alpha=0.3)
fig.savefig('fermion/fig_formfactor.pdf')
plt.close()
print("  -> fig_formfactor.pdf")

# ══════════════════════════════════════════════════════════════════════
# FIGURE 3: Charge radius vs mediator mass
# ══════════════════════════════════════════════════════════════════════

print("Figure 3: Scaling with mediator mass")
fig, ax = plt.subplots()

R_yuk = np.sqrt(3.0) / alpha_yuk
R_fer = np.sqrt(3.0) / alpha_fer
R_scl = np.sqrt(3.0) / alpha_scl

# Calibrate: R_yuk -> r_pi
m_f_phys_ref = R_yuk * hbar_c / r_pi  # MeV

m_f_range = np.logspace(np.log10(200), np.log10(200000), 200)  # MeV

# r_phys = R_nat * hbar_c / m_f_phys
r_yuk_phys = R_yuk * hbar_c / m_f_range
r_fer_phys = R_fer * hbar_c / m_f_range
r_scl_phys = R_scl * hbar_c / m_f_range

# Experimental limit
r_limit = hbar_c / 8000.0  # fm

ax.loglog(m_f_range / 1000, r_yuk_phys, 'b-', lw=2, label='Yukawa')
ax.loglog(m_f_range / 1000, r_scl_phys, 'g--', lw=2, label='Scalar loop')
ax.loglog(m_f_range / 1000, r_fer_phys, 'r-.', lw=2, label='Fermion loop')
ax.axhline(r_limit, color='k', ls=':', lw=1.5,
           label=f'$\\Lambda > 8$ TeV limit')

# Mark special masses
ax.axvline(m_f_phys_ref / 1000, color='gray', ls=':', alpha=0.5)
ax.text(m_f_phys_ref / 1000 * 1.1, 0.5, f'$m_f={m_f_phys_ref/1000:.2f}$ GeV\n(pion cal.)',
        fontsize=8, color='gray')

ax.set_xlabel('Mediator mass $m_f$ (GeV)')
ax.set_ylabel('$R_{\\mathrm{rms}}$ (fm)')
ax.set_title('Composite size vs mediator mass')
ax.set_xlim(0.2, 200)
ax.set_ylim(1e-4, 2)
ax.legend(loc='upper right')
ax.grid(True, alpha=0.3, which='both')
fig.savefig('fermion/fig_scaling.pdf')
plt.close()
print("  -> fig_scaling.pdf")

# ══════════════════════════════════════════════════════════════════════
# FIGURE 4: Spectral functions near threshold
# ══════════════════════════════════════════════════════════════════════

print("Figure 4: Spectral functions")
fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10, 4.5))

deltas = np.logspace(-4, 1, 200)
s_vals = threshold + deltas

rho_F = np.array([rho_fermion(s) for s in s_vals])
rho_S = np.array([rho_scalar(s) for s in s_vals])

# Log-log plot
ax1.loglog(deltas, rho_F, 'r-', lw=2, label='Fermion (scalar cpg, ${}^3P_0$)')
ax1.loglog(deltas, rho_S, 'g--', lw=2, label='Scalar loop')
# Reference lines
ax1.loglog(deltas, 0.01 * deltas**1.5, 'r:', alpha=0.5, label='$\\delta^{3/2}$')
ax1.loglog(deltas, 0.05 * deltas**0.5, 'g:', alpha=0.5, label='$\\delta^{1/2}$')
ax1.set_xlabel('$\\delta = s - 4m_f^2$')
ax1.set_ylabel('$\\rho(s)$')
ax1.set_title('Spectral functions')
ax1.legend(fontsize=9)
ax1.grid(True, alpha=0.3, which='both')

# Ratio plot
ratio = rho_F / np.where(rho_S > 0, rho_S, 1e-300)
ax2.loglog(deltas[rho_S > 0], ratio[rho_S > 0], 'k-', lw=2)
ax2.loglog(deltas, 0.6 * deltas**1.0, 'k:', alpha=0.5,
           label='$\\propto \\delta$ (one extra power)')
ax2.set_xlabel('$\\delta = s - 4m_f^2$')
ax2.set_ylabel('$\\rho_F / \\rho_S$')
ax2.set_title('Ratio: parity barrier effect')
ax2.legend(fontsize=9)
ax2.grid(True, alpha=0.3, which='both')

fig.tight_layout()
fig.savefig('fermion/fig_spectral.pdf')
plt.close()
print("  -> fig_spectral.pdf")

# ══════════════════════════════════════════════════════════════════════
# FIGURE 5: Binding energy scan — size ratios
# ══════════════════════════════════════════════════════════════════════

print("Figure 5: Size ratios vs binding energy")
fig, ax = plt.subplots()

E_scan = np.linspace(-0.01, -0.8, 30)
ratio_R_YF = []
ratio_R_SF = []

for E_t in E_scan:
    ly = find_lambda(V_yuk, E_t)
    lf = find_lambda(V_fer, E_t)
    ls = find_lambda(V_scl, E_t)
    if ly is None or lf is None:
        ratio_R_YF.append(np.nan)
        ratio_R_SF.append(np.nan)
        continue
    ay, _ = opt_alpha_energy(V_yuk, ly)
    af, _ = opt_alpha_energy(V_fer, lf)
    ratio_R_YF.append(af / ay)  # alpha ratio = inverse R ratio
    if ls is not None:
        a_s, _ = opt_alpha_energy(V_scl, ls)
        ratio_R_SF.append(af / a_s)
    else:
        ratio_R_SF.append(np.nan)

# alpha_fer/alpha_yuk = R_yuk/R_fer = 1/(R_fer/R_yuk)
# Plot R_fer/R_yuk = alpha_yuk/alpha_fer = 1/ratio
inv_ratio_YF = [1/r if not np.isnan(r) else np.nan for r in ratio_R_YF]
inv_ratio_SF = [1/r if not np.isnan(r) else np.nan for r in ratio_R_SF]

ax.plot(-np.array(E_scan), inv_ratio_YF, 'b-o', lw=2, ms=3,
        label='$R_{\\mathrm{fer}} / R_{\\mathrm{Yuk}}$')
ax.plot(-np.array(E_scan), inv_ratio_SF, 'g--s', lw=2, ms=3,
        label='$R_{\\mathrm{fer}} / R_{\\mathrm{scl}}$')
ax.set_xlabel('$|E_{\\mathrm{bind}}|$ (natural units)')
ax.set_ylabel('Size ratio')
ax.set_title('Form factor suppression vs binding energy')
ax.legend()
ax.grid(True, alpha=0.3)
ax.set_ylim(0, 1)
fig.savefig('fermion/fig_binding_scan.pdf')
plt.close()
print("  -> fig_binding_scan.pdf")

print("\nAll figures generated.")

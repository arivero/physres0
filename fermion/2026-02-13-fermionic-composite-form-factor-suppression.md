# Fermionic Composite Form Factor Suppression

Date: 2026-02-13 (US)
Depends on:
- `research/workspace/notes/theorems/2026-02-11-theme2-fermionic-mediation-contact-crosscheck.md`

## Motivation

SUSY-like pairing between a composite boson (e.g. pion, $\bar{q}q$)
and a fermion (e.g. muon) predicts — by compositeness transfer — that
the fermion is also composite.  Yet the muon is structureless in all
scattering experiments.

**Thesis**: this is not a paradox.  When binding is mediated by
fermionic exchange, the bound state is composite but appears
structureless in scattering, because the interaction is effectively
contact.

## I. The Angular-Momentum Argument (Qualitative)

### Bosonic exchange (spin-0 or spin-1 mediator)

The standard virtual-exchange argument:

1. A virtual boson of mass $m$ is emitted, violating energy conservation
   by $\Delta E \sim mc^2$.
2. Energy-time uncertainty: $\Delta E \cdot \Delta t \gtrsim \hbar$
   gives $\Delta t \sim \hbar/(mc^2)$.
3. The virtual particle propagates distance $R \sim c\Delta t = \hbar/(mc)$.
4. Since both $E$ and $t$ are **unbounded** variables, the only constraint
   on the range is the mass of the mediator.
5. Result: **Yukawa range** $R \sim 1/m$.

### Fermionic exchange (spin-1/2 mediator)

A fermion carries half-integer angular momentum.  The relevant
uncertainty relation involves action (angular momentum) and angle:

$$\Delta J \cdot \Delta\varphi \gtrsim \hbar$$

Key difference: **the angle $\varphi$ is compact** ($\varphi \in [0, 2\pi)$),
so $\Delta\varphi$ is bounded.  Consequences:

1. **Single-fermion exchange between scalar sources is forbidden.**
   A scalar source has $J = 0$.  Emitting a spin-1/2 particle would
   require $\Delta J = 1/2$ at the vertex, but no orbital quantum number
   $\ell$ can compensate (you cannot get $j_{\text{total}} = 0$ from
   spin-1/2 alone).  This is the selection rule proved in Theme 2.

2. **Fermion-pair exchange is required** (one-loop, minimum).  The pair
   has mass threshold $2m_f$, immediately halving the range compared to
   a single boson of the same mass.

3. **The pair's spin structure adds an angular-momentum cost** that
   further suppresses the long-distance tail.  At threshold, the fermion
   pair is non-relativistic; the spin-current contribution ($\slashed{k}$
   terms in the Dirac trace) vanishes, forcing the spectral weight to
   zero faster than for scalar pairs.

### The action-angle distinction

| Exchange type | Conjugate pair | Unbounded variable | Range |
|---|---|---|---|
| Bosonic (energy-time) | $\Delta E \cdot \Delta t \sim \hbar$ | $t$ unbounded | $R \sim 1/m$ |
| Bosonic (momentum-position) | $\Delta p \cdot \Delta x \sim \hbar$ | $x$ unbounded | $R \sim 1/m$ |
| Fermionic (action-angle) | $\Delta J \cdot \Delta\varphi \sim \hbar$ | $\varphi$ **compact** | $R \sim 1/(2m_f)$ + extra suppression |

The compactness of the angle variable is the root cause of the contact
nature: the conjugate momentum (angular momentum / action) cannot be
made arbitrarily small, so the virtual fermion cannot spread spatially.

## II. The Spectral Function Proof (Quantitative)

### Setup

Consider the Yukawa model $\mathcal{L} \supset g\,\phi\,\bar\psi\psi$
with scalar source $\phi$ and Dirac fermion $\psi$ of mass $m_f$.

The static potential between two $\phi$ sources comes from the one-loop
vacuum polarization $\Pi(q^2)$.  The spectral (Kallen-Lehmann)
representation gives:

$$V(r) = -\frac{1}{4\pi r}\int_{4m_f^2}^{\infty} \frac{ds}{2\pi}\,
\rho(s)\,e^{-\sqrt{s}\,r},$$

where $\rho(s) = 2\,\mathrm{Im}\,\Pi(s)$ is the spectral function.

### Proposition 1 (Fermion loop spectral function near threshold)

For the $g\phi\bar\psi\psi$ coupling, the spectral function near the
$2m_f$ threshold ($s = 4m_f^2 + \delta$, $\delta \to 0^+$) is:

$$\rho_F(\delta) \propto \delta^{3/2}.$$

### Proof

The imaginary part of the one-loop $\phi$ self-energy from a fermion loop is:

$$\mathrm{Im}\,\Pi_F(s) = -\frac{g^2}{24\pi}\,
\frac{(s - 4m_f^2)^{3/2}}{s^{1/2}}.$$

**Derivation**: The Dirac trace gives
$\mathrm{Tr}[(\slashed{k}+m_f)(\slashed{k}+\slashed{q}+m_f)]
= 4[k\cdot(k+q) + m_f^2]$.
After Feynman parameterization, the spectral function in the physical
region $s > 4m_f^2$ is:

$$\mathrm{Im}\,\Pi_F(s) = \frac{g^2}{4\pi}
\int_{x_-}^{x_+} dx\,[m_f^2 - x(1-x)s],$$

where $x_\pm = (1 \pm \beta)/2$, $\beta = \sqrt{1 - 4m_f^2/s}$.
Evaluating the integral with $x_+ - x_- = \beta$,
$x_+x_- = m_f^2/s$:

$$\int_{x_-}^{x_+} dx\,[m_f^2 - x(1-x)s]
= -\frac{\beta(s - 4m_f^2)}{6}.$$

Since $\beta = \sqrt{(s-4m_f^2)/s}$, we get
$\mathrm{Im}\,\Pi_F \propto (s-4m_f^2)^{3/2}$.

The exponent $3/2$ (not $1/2$) arises because the Dirac trace factor
$[m_f^2 - x(1-x)s]$ vanishes at threshold ($s = 4m_f^2$), contributing
an extra power of $(s - 4m_f^2)$ beyond the phase-space factor
$\beta \sim (s-4m_f^2)^{1/2}$.  $\square$

### Proposition 2 (Scalar loop spectral function — comparison)

For a scalar mediator loop ($g_s\,\phi\,|\chi|^2$ with complex scalar
$\chi$ of mass $m$), the spectral function near threshold is:

$$\rho_S(\delta) \propto \delta^{1/2}.$$

### Proof

The scalar loop has no Dirac numerator structure.  The imaginary part
from two-body phase space alone gives
$\mathrm{Im}\,\Pi_S(s) \propto \sqrt{s - 4m^2} = \delta^{1/2}$.  $\square$

### Proposition 3 (Long-distance tail)

Near threshold, set $s = 4m^2 + \delta$ with
$\sqrt{s} \approx 2m + \delta/(4m)$.  The potential becomes:

$$V(r) \sim -\frac{e^{-2mr}}{4\pi r}\int_0^{\infty}
\frac{d\delta}{2\pi}\,\rho(\delta)\,e^{-\delta r/(4m)}.$$

If $\rho(\delta) \sim \delta^{\alpha}$, the Laplace transform gives:

$$\int_0^{\infty}\delta^{\alpha}\,e^{-\delta r/(4m)}\,d\delta
= \Gamma(\alpha+1)\,\left(\frac{4m}{r}\right)^{\alpha+1}.$$

Including the $1/(4\pi r)$ kernel:

| Loop type | Threshold $\alpha$ | Tail behavior |
|---|---|---|
| Scalar ($\chi$) | $1/2$ | $V \sim e^{-2mr}/r^{5/2}$ |
| **Fermion ($\psi$)** | **3/2** | $V \sim e^{-2mr}/r^{7/2}$ |

**The fermion loop tail falls off one full power of $r$ faster than the
scalar loop tail, at the same mass.**  This extra power comes directly
from the spin-1/2 Dirac trace structure.  $\square$

### Remark: correction to Theme 2

Theme 2 stated the tail as $e^{-2m_f r}/r^5$.  The spectral-function
calculation gives $e^{-2m_f r}/r^{7/2}$.  The qualitative conclusion
(fermionic tail is steeper than bosonic) is unchanged; the quantitative
exponent is corrected here.

## III. Why the Muon Looks Structureless

Combining the qualitative and quantitative arguments:

1. **No single-fermion exchange** (angular momentum selection rule):
   the lightest exchange process requires a fermion pair, setting the
   range to $\sim 1/(2m_f)$ instead of $1/m_f$.

2. **Steeper tail** ($\delta^{3/2}$ vs $\delta^{1/2}$): the spin trace
   forces the spectral function to vanish faster at threshold.  The
   position-space potential falls as $e^{-2m_f r}/r^{7/2}$ (fermion)
   instead of $e^{-2mr}/r^{5/2}$ (scalar).

3. **Compact conjugate variable**: the action-angle uncertainty
   $\Delta J \cdot \Delta\varphi \gtrsim \hbar$ with bounded $\varphi$
   prevents the fermionic exchange from spreading spatially.  The
   spectral threshold suppression is the quantitative manifestation
   of this kinematic constraint.

The combination means that a composite state bound by fermionic exchange
has a form factor $F_1(q^2)$ that deviates from unity (the point-particle
value) only at momentum transfers $q$ much higher than for a bosonic
composite of the same binding energy.

**A muon-like particle can be composite (satisfying SUSY compositeness
transfer from the pion) while appearing structureless in scattering,
because its binding is fermionic.**

## IV. Form Factor of a Composite Fermion

### Definition

The electromagnetic form factor of a spin-1/2 particle:

$$\langle p' | J^\mu | p \rangle
= \bar{u}(p')\left[
  F_1(q^2)\,\gamma^\mu + \frac{i\sigma^{\mu\nu}q_\nu}{2M}\,F_2(q^2)
\right]u(p).$$

For a point particle: $F_1(q^2) = 1$, $F_2 = 0$ at tree level.

### Compositeness signature

If the particle has internal structure with characteristic size $R$:

$$F_1(q^2) \approx 1 - \frac{1}{6}\langle r^2 \rangle\,q^2 + \cdots,$$

where $\langle r^2 \rangle$ is the mean-square charge radius.

### Bound on charge radius for fermionic binding

For a bound state in $V(r) \sim e^{-\mu r}/r^p$ at the same binding
energy as a Yukawa ($p=1$) state, the charge radius ratio scales as:

$$\frac{\langle r^2 \rangle_{p}}{\langle r^2 \rangle_{1}}
\sim \frac{1}{\mu^{2}} \cdot \frac{g(p)}{g(1)},$$

where $g(p)$ is a decreasing function of $p$ (steeper potentials
compress the wave function).  For fermion-mediated ($p = 7/2$) vs
scalar-mediated ($p = 5/2$) at equal mass: additional compression.

## Validation Contract

### Assumptions

1. Perturbative one-loop exchange (weak coupling).
2. Static limit (no recoil).
3. Dirac fermion (Majorana case similar, different combinatorics).
4. Non-relativistic Schrodinger equation for the bound-state form factor
   estimate (valid when binding energy $\ll$ constituent mass).

### Units and dimensions check

1. $[\Pi(s)]$ dimensionless in 4D with Yukawa coupling $[g] = 1$
   (natural units).
2. $[\rho(s)] = [s^0]$ (dimensionless spectral weight per unit $s$).
3. Threshold exponents ($\alpha = 1/2, 3/2$) are dimensionless.
4. $[V(r)] = [\text{energy}]$: verified from
   $[g^2/(4\pi r) \cdot (4m/r)^{\alpha+1}]$ with appropriate mass
   dimensions.

### Symmetry/conservation checks

1. $J$ conservation at vertices: single fermion exchange between scalar
   sources forbidden (requires $\Delta J = 1/2$, impossible).
2. Spectral function positivity ($\rho > 0$ for $s > 4m_f^2$): unitarity.
3. Fermion number conservation: even number of fermion lines in loop.

### Independent cross-check path

Run:

```bash
python3.12 fermion/fermionic_composite_form_factor_check.py
```

### Confidence statement

High confidence on Propositions 1-3 (standard one-loop QFT, Feynman
parameterization, Laplace asymptotics).

Medium confidence on the qualitative action-angle argument (Section I),
which provides correct physical intuition but is not itself a theorem.
The spectral function proof (Section II) is the rigorous backing.

### Reproducibility metadata

1. Python 3.12, numpy, scipy.
2. Date anchor: 2026-02-13 (US).

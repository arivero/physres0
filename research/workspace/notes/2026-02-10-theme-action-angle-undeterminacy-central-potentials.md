# Theme: Action–Angle “Undeterminacy” for Central Potentials

Date: 2026-02-10 (US)

## Question

What is the precise content of an “action–angle undeterminacy principle” in quantum mechanics,
and how should it be stated/checked for *central potentials*?

Here “undeterminacy” means: action variables and angle variables are canonically conjugate,
so sharp knowledge of one implies delocalization/uncertainty of the other (with caveats for periodic angles).

## What our conversation already contains (internal anchors)

1. **Bohr–Sommerfeld via Newton/area language (central forces):**
   `conv_patched.md:1779` frames quantization for circular/bound motion using an “area swept per unit time” principle,
   explicitly stated as applicable to *any central force*.
2. **Action as symplectic area (canonical 1-form):**
   `conv_patched.md:2214` introduces the action variable
   \[
   J=\oint p\,dq
   \]
   and interprets it as (signed) area in phase space, emphasizing additivity and refinement stability.

These two anchors are already the classical/semiclassical bridge:
action integrals are the objects that (i) add under concatenation and (ii) become quantized in old/EBK quantization.

## Minimal technical dictionary (decision points)

### Classical action–angle variables

For an integrable Hamiltonian system with invariant tori, one can choose coordinates \((J_i,\theta_i)\) such that
\[
\{\theta_i,J_j\}=\delta_{ij},\qquad \theta_i\in\mathbb T,\ J_i\in\mathbb R.
\]
For **central potentials** in 3D, standard actions include:
- \(J_\phi = L_z\),
- \(J_\theta = L-|L_z|\),
- \(J_r = \frac{1}{\pi}\int_{r_{\min}}^{r_{\max}} p_r(r;E,L)\,dr\),
with corresponding angle variables \((\theta_r,\theta_\theta,\theta_\phi)\).

### Quantum “angle operator” caveat (periodicity)

Because angles are periodic, a globally self-adjoint \(\hat\theta\) with spectrum on \([0,2\pi)\) is subtle.
Practical options (to be chosen explicitly when we promote this theme):
1. use the unitary \(\hat U := e^{i\hat\theta}\) and its commutation with \(\hat J\),
2. use an angle POVM (measurement-theory route),
3. restrict to local charts / semiclassical wavepackets where \(\theta\) behaves approximately as a coordinate.

The “undeterminacy principle” should be phrased in the chosen language (not hand-waved).

## One concrete cross-check (symbolic, paper-ready)

For a 1D harmonic oscillator (a canonical action–angle example),
\[
H=\frac{p^2}{2m}+\frac12 m\omega^2 q^2,
\]
the classical orbit is an ellipse in \((q,p)\) with area
\[
J=\oint p\,dq = \frac{2\pi E}{\omega}.
\]
Bohr–Sommerfeld/EBK quantization takes the form
\[
J = 2\pi\hbar\left(n+\frac12\right),
\]
so
\[
E_n=\hbar\omega\left(n+\frac12\right),
\]
which matches the exact quantum spectrum.

This is the cleanest “action quantization” witness and pins units unambiguously.

## How this becomes a central-potential deliverable

Deliverable target:
one short note (or appendix section) stating:

1. action–angle variables for central potentials (\(J_r,J_\theta,J_\phi\)),
2. the semiclassical quantization condition (EBK) with Maslov indices stated,
3. a clear, defensible “action–angle uncertainty” phrasing (angle periodicity handled),
4. one worked example (Coulomb or isotropic oscillator) cross-checked against known spectra.

Optional bridge:
tie \(J_\phi=L_z\) to the standard \(\phi\)–\(L_z\) conjugacy (and its circular-uncertainty variant),
making the “angle–angular-momentum” case the central-potential entry point.

## Validation Contract

### Assumptions

1. Central potential means rotationally invariant Hamiltonian \(H(p,r)\).
2. “Action–angle variables” assumes integrability (true for standard central potentials).
3. Any “uncertainty” statement must respect angle periodicity (no naive global self-adjoint \(\hat\theta\) claim unless proved).

### Units and dimensions check

1. \(J\) has units of action (energy × time), same as \(\hbar\).
2. \(\theta\) is dimensionless; thus \(\Delta\theta\,\Delta J\) has units of action.

### Symmetry/conservation checks

1. Rotational invariance ⇒ conservation of \(\mathbf L\); hence \(J_\phi\) is conserved.
2. Time-translation invariance ⇒ conservation of \(E\), which parametrizes the radial action \(J_r(E,L)\).

### Independent cross-check path

Symbolic cross-check included above (harmonic oscillator action integral + EBK reproduces exact spectrum).
Next cross-check (queued): Coulomb/Kepler central potential \(J_r\) computation and spectrum comparison.

### Confidence statement

High confidence on the action-integral/EBK cross-check logic; medium confidence on the fastest rigorous “angle uncertainty” formalization path without bringing in external references (POVM vs unitary vs semiclassical chart).

### Reproducibility metadata

- host repo: `/Users/arivero/physbook`
- source anchors: `conv_patched.md:1779`, `conv_patched.md:2214`
- date anchor: 2026-02-10 (US)

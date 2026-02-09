# Paper 1: Static Variational Consistency via Probability Amplitudes

Date: 2026-02-09

## Working Title

Static Variational Consistency, Probability Amplitudes, and Equivalence to Quantum Mechanics Without Time Evolution

## Abstract

This paper establishes a static variational-consistency theorem in a
stationary-phase regime. The core result is that, for a nondegenerate critical
set, the oscillatory probability amplitude
\[
A_\varepsilon(O)=\varepsilon^{-1/2}\int e^{\frac{i}{\varepsilon}f(x)}O(x)\,dx
\]
admits a stationary-phase expansion. In the single-critical-point case (or
after explicit averaging that removes interference between distinct critical
points), the modulus-square recovers the variational localization measure:
\[
|A_\varepsilon(O)|^2 \to 2\pi\langle \delta(f'),|O|^2\rangle.
\]
This yields a static equivalence to the measurement layer of quantum mechanics
(Born-type map) without invoking time evolution. Geometric \(1/2\)-density
language is included as an optional kernel-level representation, not as a
replacement for analytic control.

## Scope and Claim

In-scope claim:

1. amplitude-to-density map,
2. critical-point weighting,
3. static expectation assignment.

Out of scope:

1. dynamics on time histories,
2. interacting continuum field-theory existence,
3. scattering and unitary real-time evolution.

## Setup

Let \(f\in C^\infty(\mathbb R)\) and \(O\in C_c^\infty(\mathbb R)\). Define
\[
A_\varepsilon(O):=\varepsilon^{-1/2}\int_{\mathbb R} e^{\frac{i}{\varepsilon}f(x)}O(x)\,dx,\qquad \varepsilon>0.
\]

The static localization object is \(\delta(f')\), interpreted as a pullback of
Dirac mass by \(f'\), not as \(\delta'\).

## Main Theorem Package

1. **Critical-point decomposition theorem.**  
   If \(f'\) has isolated simple zeros \(\{x_i\}_{i=1}^N\), then
   \[
   \delta(f')=\sum_{i=1}^N\frac{\delta(x-x_i)}{|f''(x_i)|}.
   \]
2. **Diagonal Born recovery with interference caveat.**  
   In the single-critical-point support case:
   \[
   |A_\varepsilon(O)|^2
   \to
   2\pi\,\frac{|O(x_0)|^2}{|f''(x_0)|}
   =
   2\pi\langle\delta(f'),|O|^2\rangle.
   \]
   For multiple critical points, diagonal terms still produce the same weighted
   sum while cross terms are oscillatory and need explicit averaging/coarse
   graining for convergence when contributing critical values are pairwise
   distinct. If some critical values coincide, coherent same-phase terms must be
   grouped before averaging.
3. **Static QM measurement-layer equivalence.**  
   In the single-point case, or after explicit coarse graining in the
   nonresonant multi-point case, the induced map is
   \[
   \mathcal B_f(O)=2\pi\langle\delta(f'),|O|^2\rangle,
   \]
   which is a static Born-type assignment without a time-evolution operator.

## Geometric Representation Note

For kernel composition on manifolds/groupoids, the same amplitude object can be
represented as a geometric \(1/2\)-density (or half-form in
geometric-quantization contexts). This representation is kinematic and
coordinate-free for convolution, but does not by itself prove continuum-limit
convergence.

## Validation Contract

1. **Assumptions:** finite nondegenerate critical set, explicit observable class,
   fixed branch \(\varepsilon\to0^+\), and in the multi-point averaged branch:
   nonresonant critical-value gaps or explicit coherent-block handling.
2. **Units/dimensions:** phase \(f/\varepsilon\) dimensionless; normalization
   \(\varepsilon^{-1/2}\) matches 1D stationary phase.
3. **Symmetry checks:** invariance under \(f\mapsto f+\mathrm{const}\), and
   coordinate consistency of geometric representation.
4. **Independent checks:**
   - analytic stationary-phase derivation,
   - numeric diagnostics:
     - `python3.12 research/workspace/simulations/claim1_halfdensity_static_check.py`,
     - `python3.12 research/workspace/simulations/claim1_point_supported_scaling_modes.py`,
     - `python3.12 research/workspace/simulations/claim1_pair_groupoid_convolution_check.py`,
   - optional formal-companion finite-model increment template:
     - `research/workspace/proofs/Claim1lean/FiniteExponentialIncrementBound.lean`,
     - `research/workspace/proofs/Claim1lean/FiniteExponentialRegularity.lean`.
5. **Confidence statement:** theorem-grade in the scoped static regime.

## Reproducibility Metadata

1. TeX engine tested in this workspace: `/Library/TeX/texbin/pdflatex` (TeX Live 2025),
2. safe build script: `~/.codex/skills/pdflatex-safe-build/scripts/build_pdflatex_safe.sh`,
3. date anchor: 2026-02-09 (US).

## Conclusion

Static variational consistency is proved in a self-contained theorem chain:
critical-point decomposition, diagonal/averaged Born recovery, and static
measurement-layer equivalence. The geometric \(1/2\)-density discussion is
retained as a kinematic representation layer, separate from dynamical or
field-level convergence claims.

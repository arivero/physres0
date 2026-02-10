# Claim 1 Support (Newton-Limit Paradox): Kernel Semigroup Normalization and the `t^{-d/2}` Exponent

Date: 2026-02-10 (US)

Lean modules:

- `research/workspace/proofs/Claim1lean/GaussianSemigroupNormalization.lean` (1D measure + diagonal prefactor anchor)
- `research/workspace/proofs/Claim1lean/GaussianSemigroupNormalizationNd.lean` (product/exponent form for `d` dimensions)
- `research/workspace/proofs/Claim1lean/SchurComplementDeterminant.lean` (determinant prefactor identity)
- `research/workspace/proofs/Claim1lean/SchurComplementElimination.lean` (LDU/elimination template)

Numeric diagnostic:

- `python3.12 research/workspace/simulations/claim1_gaussian_kernel_semigroup_td2_check.py`

## Goal

Pin down, in a form suitable for manuscript citation, the mechanism:

1. **semigroup composition fixes the variance parameter** (additivity under convolution),
2. **mass normalization fixes the diagonal exponent** and forces the universal `t^{-d/2}` scaling,
3. **integrating out/intermediate-variable elimination** produces a Schur-complement reduced block plus a determinant prefactor (Van Vleck / Gaussian elimination template).

This is a support lane for the “Newton-limit paradox” framing: *refinement + composition are rigid enough to force square-root normalization exponents*, naturally living at the amplitude/half-density level.

## Mathematical statement (Euclidean kernel)

Work on `R^d`. Consider translation-invariant Gaussian kernels
\[
K_t(x)=a(t)\exp\!\left(-\frac{|x|^2}{4\,b(t)}\right),\qquad t>0,
\]
with `a(t)>0`, `b(t)>0`, and assume:

1. **Semigroup:** `K_{t+s} = K_t * K_s` for all `t,s>0`.
2. **Normalization:** `∫ K_t = 1` for all `t>0`.
3. **Regularity:** `b(t)` is continuous (to rule out Cauchy-equation pathologies).

Then `b(t)` is additive, hence `b(t)=σ t`, and normalization forces
\[
K_t(0) = a(t) \propto b(t)^{-d/2} \propto t^{-d/2}.
\]

This is the clean Euclidean witness for the universal exponent `d/2`.

## Lean anchors (what is machine-checked)

### 1) 1D Gaussian semigroup + diagonal prefactor

`Claim1lean/GaussianSemigroupNormalization.lean` re-exports mathlib statements:

- measure-level convolution semigroup (variance adds),
- diagonal density value `p_v(0) = 1 / sqrt(2π v)` and its explicit factorization.

### 2) `d`-dimensional exponent as a product law

`Claim1lean/GaussianSemigroupNormalizationNd.lean` packages the algebraic “product/exponent” form:

\[
\big(p_v(0)\big)^d = \Big(\frac{1}{\sqrt{2\pi}}\Big)^d \Big(\frac{1}{\sqrt v}\Big)^d,
\]
making the `v^{-d/2}` scaling transparent without requiring multivariate measure theory.

### 3) Schur complement elimination (no analysis)

`Claim1lean/SchurComplementDeterminant.lean` provides the determinant identity
\[
\det\begin{pmatrix}A & B\\ C & D\end{pmatrix}=\det(A)\det\!\big(D-CA^{-1}B\big)
\]
under an invertible pivot.

`Claim1lean/SchurComplementElimination.lean` provides the LDU/elimination decomposition
(`Matrix.fromBlocks_eq_of_invertible₁₁` rewrapped):
left/right multiplication by block-unit-triangular matrices reduces `[A B; C D]` to the Schur complement block `D-CA^{-1}B`.

## Independent cross-check (numeric)

`claim1_gaussian_kernel_semigroup_td2_check.py` performs:

1. Monte Carlo verification of `K_t * K_s ≈ K_{t+s}` at representative points for `d=1,2,3,4`,
2. exact log-log slope check of `K_t(0)` against the forced exponent `-d/2`.

This is a sanity check only; it does not replace analytic control.

## Validation Contract

### Assumptions

1. Euclidean (positive-time) Gaussian kernels with convolution semigroup property.
2. Mass normalization `∫K_t=1`.
3. Continuity/measurability assumptions sufficient to solve the Cauchy additivity constraint for `b(t)`.
4. No oscillatory/Feynman `i0` claims are made in this note.

### Units and dimensions check

- If `x` has units of length, then `K_t(x)` has units `length^{-d}` so that `∫ K_t dx` is dimensionless.
- `b(t)` has units of `length^2` (variance parameter); therefore `K_t(0) ∝ b(t)^{-d/2}` has units `length^{-d}`.

### Symmetry checks

- Translation invariance is built in (kernel depends on `x-y` in convolution form).
- Rotation invariance holds for the isotropic Gaussian `|x|^2` kernel (Euclidean symmetry).

### Independent cross-check path

1. Lean build:
   - `cd research/workspace/proofs && /Users/arivero/.elan/bin/lake build Claim1lean.GaussianSemigroupNormalizationNd`
   - `cd research/workspace/proofs && /Users/arivero/.elan/bin/lake build Claim1lean.SchurComplementElimination`
2. Python diagnostic:
   - `python3.12 research/workspace/simulations/claim1_gaussian_kernel_semigroup_td2_check.py`

### Confidence statement

High confidence for the Euclidean Gaussian `t^{-d/2}` exponent forcing mechanism and the Schur-complement elimination template (both standard and now mechanically anchored). Medium confidence for any oscillatory continuation claims until a separate analytic regularization note is completed.

### Reproducibility metadata

1. repo: `/Users/arivero/physbook`
2. date anchor: 2026-02-10 (US)
3. shell: `zsh`
4. Python: `python3.12`
5. Lean: `/Users/arivero/.elan/bin/lean` via `lake` in `research/workspace/proofs`


# Claim 1 Support (Newton-Limit Paradox): Lean Gaussian Semigroup + Prefactor (1D)

Date: 2026-02-10 (US)  
Lean module: `research/workspace/proofs/Claim1lean/GaussianSemigroupNormalization.lean`

## Goal

Record a machine-checked anchor for the Gaussian “normalization is forced by composition” lane:

1. the mean-zero Gaussian family forms a convolution semigroup (variance adds),
2. the corresponding density has the characteristic `v^{-1/2}` prefactor in 1D.

This is one concrete component of the `t^{-d/2}` normalization target mentioned in:

- `research/workspace/notes/2026-02-10-newton-limit-paradox-quantum-necessity.md`

## Machine-Checked Statements (Lean)

### 1) Convolution semigroup (measure level)

`Claim1lean.gaussianReal_conv_zero` proves:

\[
\mathcal N(0,v_1)\ast \mathcal N(0,v_2)=\mathcal N(0,v_1+v_2)
\]

in the mathlib `Measure` sense using
`ProbabilityTheory.gaussianReal_conv_gaussianReal`.

### 2) Prefactor scaling at the diagonal (density at 0)

`Claim1lean.gaussianPDFReal_zero_at_zero` proves:

\[
p_{v}(0)=\frac{1}{\sqrt{2\pi v}},
\]

in the exact mathlib normalization (`gaussianPDFReal`) for `v : ℝ≥0`.

This is the 1D instance of the `t^{-d/2}` scaling theme:
in higher dimensions, product structure gives the exponent `d/2`.

### 3) Normalization (integral equals 1)

`Claim1lean.integral_gaussianPDFReal_eq_one_zero_mean` re-exports the standard fact:

\[
\int_{\mathbb R} p_v(x)\,dx = 1 \qquad (v\ne 0).
\]

## Why This Matters Here

This file supplies the “exact Gaussian witness” that kernel composition by convolution
imposes very rigid normalization behavior:

1. semigroup consistency is not optional (variance must add),
2. diagonal normalization exhibits the characteristic square-root exponent already in 1D.

This is intended to be paired with:

- the semigroup→generator lemma (`Claim1lean/SemigroupGenerator.lean`),
- the Schur-complement determinant template (`Claim1lean/SchurComplementDeterminant.lean`),

to build the Newton-limit paradox story: composition + refinement forces prefactors that
naturally live at the amplitude/half-density level.

## Next Tightening Targets

1. Upgrade from measure-level semigroup to an explicit *kernel* convolution identity
   (density-level), with hypotheses stated so the oscillatory `i0` branch can be treated.
2. Lift from 1D to `d` dimensions, recording the `t^{-d/2}` prefactor explicitly.
3. Connect the Gaussian prefactor to the Van Vleck / mixed-Hessian determinant lane
   via the Schur-complement elimination template.


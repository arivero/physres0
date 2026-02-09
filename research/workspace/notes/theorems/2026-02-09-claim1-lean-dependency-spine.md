# Claim 1 Phase BB (AN-13): Lean Dependency Spine for B5

Date: 2026-02-09 (CET)

## Goal

Provide a compact module-level map from Lean results (AU→BA) to the \(d=3\) B5 bridge obligations.

## Lean Spine (Current)

1. `Claim1lean/CInvariant.lean` (AU)
   - exact \(c\)-invariance under \(\tau\)-reparameterization.
2. `Claim1lean/SmallKappaLipschitz.lean` (AU)
   - interval increment from derivative bound: `O(κ)` control.
3. `Claim1lean/CovarianceDerivative.lean` (AV)
   - quotient derivative in covariance form for \(\omega=N/Z\).
4. `Claim1lean/FiniteCovarianceBound.lean` (AW)
   - finite centered-product covariance inequality template.
5. `Claim1lean/RatioStateDerivativeBound.lean` (AX)
   - AN-7 + AN-8 combined into abstract `|∂ω|` bound.
6. `Claim1lean/RatioStateIncrementBound.lean` (AY/AZ/BA)
   - interval increment bound from derivative template,
   - interior `derivWithin = deriv` bridge,
   - one-sided boundary bridge at \(t=0\), \(\kappa>0\).

## Mapping to B5 Obligations (Phase AS)

Recall B5 target:
\[
|\omega_\kappa(F)-\omega_0(F)|\le C_F\kappa.
\]

Lean coverage now:

1. derivative-control skeleton for ratio states: covered (AV/AX),
2. conversion from derivative bound to interval increment: covered (AU/AY),
3. boundary/interior technical glue for interval domain: covered (AZ/BA).

## Next Missing Machine-Checked Ingredient

Still missing for direct B5 closure in a field-like class:

1. a Lean bridge from concrete integral/model assumptions to the AN-7 derivative hypotheses
   (`HasDerivAt N ...`, `HasDerivAt Z ...`, representation hypothesis) in a reusable theorem.

This is the next formal target.

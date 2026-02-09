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
7. `Claim1lean/FiniteExponentialFamilyDeriv.lean` (BC)
   - finite exponential-family derivative bridge (`N'=-A`, `Z'=-B`).
8. `Claim1lean/FiniteExponentialRepresentation.lean` (BD)
   - finite exponential-family centered representation bridge for
     \((A/Z)-\omega(B/Z)\).
9. `Claim1lean/FiniteExponentialDerivativeBound.lean` (BE)
   - finite exponential-family model-internal derivative bounds for \(\omega=N/Z\).

## Mapping to B5 Obligations (Phase AS)

Recall B5 target:
\[
|\omega_\kappa(F)-\omega_0(F)|\le C_F\kappa.
\]

Lean coverage now:

1. derivative-control skeleton for ratio states: covered (AV/AX),
2. conversion from derivative bound to interval increment: covered (AU/AY),
3. boundary/interior technical glue for interval domain: covered (AZ/BA),
4. derivative hypotheses from concrete finite exponential models: covered (BC),
5. centered representation side from concrete finite exponential models: covered (BD),
6. model-specific derivative bound corollaries from concrete finite exponential models: covered (BE).

## Next Missing Machine-Checked Ingredient

Still missing for direct B5 closure in a field-like class:

1. a Lean interval-increment corollary specialized to the finite exponential
   class that imports BE derivative control over \([0,\kappa]\) into AN-10-style
   `Cκ` bounds (AN-17 target).

This is the next formal target.

# Claim 1 Phase AU: Lean Formalization Status and Priority Rule

Date: 2026-02-09 (CET)

## Goal

Record the first machine-checked Lean formalization artifacts and lock validation priority.

## Lean Workspace

- Root: `research/workspace/proofs/`
- Toolchain:
  - `/Users/arivero/.elan/bin/lean`
  - `/Users/arivero/.elan/bin/lake`
- Dependency:
  - `mathlib` configured and fetched via `lake update`.

## Machine-Checked Modules (Current)

1. `Claim1lean/CInvariant.lean`
   - defines `Params`, `cParam`, and `tau`,
   - proves exact \(c\)-invariance under nonzero `tau` scaling,
   - proves `tau` composition and inverse structure,
   - proves observable invariance when observable depends only on `cParam`.
2. `Claim1lean/SmallKappaLipschitz.lean`
   - proves derivative-bound implies \(O(\kappa)\) increment on \([0,\kappa]\),
   - provides unit-interval specialization.
3. `Claim1lean/CovarianceDerivative.lean`
   - proves quotient-derivative identity in covariance form for \(\omega=N/Z\),
   - gives both expanded and factored forms used in AN-5 reasoning.
4. `Claim1lean/FiniteCovarianceBound.lean`
   - proves finite-support centered-product covariance bounds for uniform averages,
   - provides machine-checked inequality templates feeding small-\(\kappa\) control.
5. `Claim1lean/RatioStateDerivativeBound.lean`
   - combines quotient-derivative covariance identity with centered-product bound,
   - yields an abstract machine-checked `|∂ω|` control template.
6. `Claim1lean/RatioStateIncrementBound.lean`
   - lifts pointwise derivative control to interval increment bounds,
   - provides the machine-checked B5-shape \(|\omega(\kappa)-\omega(0)|\lesssim C\kappa\) bridge,
   - includes interior `derivWithin = deriv`,
   - includes one-sided boundary bridge `Icc`↔`Ici` at \(0\) for \(\kappa>0\).
7. `Claim1lean/FiniteExponentialFamilyDeriv.lean`
   - formalizes a concrete finite-sum exponential-family model class,
   - proves `HasDerivAt` bridges `N'=-A` and `Z'=-B` in that class,
   - discharges the AN-7 derivative-shape assumptions from explicit model data.
8. `Claim1lean/FiniteExponentialRepresentation.lean`
   - formalizes a centered representation bridge for the same finite exponential family,
   - rewrites \((A/Z)-\omega(B/Z)\) as weighted centered sums (raw and normalized-weight forms),
   - discharges the AN-13 missing representation ingredient in concrete finite models.
9. `Claim1lean/FiniteExponentialDerivativeBound.lean`
   - combines AN-14 derivative bridge and AN-15 centered representation in a concrete model class,
   - proves model-internal \(|\omega'|\) bounds (general weighted-absolute and centered-\(K\) forms).
10. `Claim1lean/FiniteExponentialIncrementBound.lean`
   - combines AN-16 derivative control with AN-10 interval machinery,
   - proves finite exponential-family `Cκ` interval-increment control under explicit uniform interval assumptions.
11. `Claim1lean/FiniteExponentialRegularity.lean`
   - proves automatic finite-model regularity facts for the same class:
     `Zsum > 0`, `Zsum ≠ 0`, global differentiability of `Nsum/Zsum`,
   - provides a reusable interval bridge `derivWithin = deriv` on `Icc(0,κ)` for `κ>0`.
12. `Claim1lean/FiniteExponentialIncrementBound.lean` (AN-18 wrapper)
   - adds `omegaExp_increment_bound_of_uniform_centered_control_auto`,
   - discharges BF regularity side-assumptions (`hDiff`, `hwithin`, `hZ`) from intrinsic finite-model structure,
   - reduces hypotheses to nonnegativity plus centered and moment controls.
13. `Claim1lean/FiniteExponentialIncrementBound.lean` (AN-22 wrapper)
   - adds `omegaExp_increment_bound_of_uniform_centered_control_auto_renormalizedScale`,
   - injects \(a^3\)-rescaled (renormalized) moment channels directly into the AN-18 increment shape,
   - keeps the increment theorem form unchanged while moving scaling choices into the `s`-channel map.

## Relation to Current Claim 1 Queue

These formalizations support:

1. the \(c\)-invariance backbone used in AL/AP/AQ notes,
2. the AN-5 B5-prototype inequality pattern (small-\(\kappa\) Lipschitz step),
3. the AN-14 finite-dimensional derivative-under-sum bridge from concrete model assumptions to AN-7 hypotheses,
4. the AN-15 finite-dimensional centered-representation bridge from concrete model assumptions to AN-9 representation side,
5. the AN-16 model-internal derivative-bound corollary for the finite exponential family,
6. the AN-17 model-internal interval-increment `Cκ` corollary for the finite exponential family,
7. the AN-18 automatic-regularity collapse from BF hypotheses to minimal model-data bounds.

## Next Lean Target (Queued)

AN-31 (Lean support lane): extend finite-index AN-30 packaging to uniformly
locally finite exhaustion families with summability-weighted combinatorial
constants and projective-consistency interfaces between exhaustion levels.

## Validation Priority (Locked)

For new Claim 1 theorem upgrades:

1. attempt Lean formalization first when scope is compatible,
2. use symbolic derivations next,
3. use numeric scripts as complementary diagnostics.

## Build Commands

```bash
cd research/workspace/proofs
/Users/arivero/.elan/bin/lake build Claim1lean.CInvariant
/Users/arivero/.elan/bin/lake build Claim1lean.SmallKappaLipschitz
/Users/arivero/.elan/bin/lake build Claim1lean.CovarianceDerivative
/Users/arivero/.elan/bin/lake build Claim1lean.FiniteCovarianceBound
/Users/arivero/.elan/bin/lake build Claim1lean.RatioStateDerivativeBound
/Users/arivero/.elan/bin/lake build Claim1lean.RatioStateIncrementBound
/Users/arivero/.elan/bin/lake build Claim1lean.FiniteExponentialFamilyDeriv
/Users/arivero/.elan/bin/lake build Claim1lean.FiniteExponentialRepresentation
/Users/arivero/.elan/bin/lake build Claim1lean.FiniteExponentialDerivativeBound
/Users/arivero/.elan/bin/lake build Claim1lean.FiniteExponentialRegularity
/Users/arivero/.elan/bin/lake build Claim1lean.FiniteExponentialIncrementBound
```

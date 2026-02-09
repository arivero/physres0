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

## Relation to Current Claim 1 Queue

These formalizations support:

1. the \(c\)-invariance backbone used in AL/AP/AQ notes,
2. the AN-5 B5-prototype inequality pattern (small-\(\kappa\) Lipschitz step),
3. the AN-14 finite-dimensional derivative-under-sum bridge from concrete model assumptions to AN-7 hypotheses.

## Next Lean Target (Queued)

AN-15: formalize the missing representation bridge (centered/covariance form for the finite exponential-family ratio state), so AN-14 assumptions feed AN-9/AN-10 without extra manual representation hypotheses.

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
```

# Claim1 Lean Workspace

Date: 2026-02-09 (CET)

This folder hosts Lean 4 formalizations for Claim 1.

## Toolchain

- Lean/Lake binary path:
  - `/Users/arivero/.elan/bin/lean`
  - `/Users/arivero/.elan/bin/lake`
- Pinned toolchain: see `lean-toolchain`.
- `mathlib` is configured in `lakefile.toml`.

## Setup

```bash
cd research/workspace/proofs
/Users/arivero/.elan/bin/lake update
```

## Build

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
/Users/arivero/.elan/bin/lake build Claim1lean.FiniteExponentialIncrementBound
/Users/arivero/.elan/bin/lake build Claim1lean.WeightedLocalGraphDecay
```

## Current formalized modules

- `Claim1lean/CInvariant.lean`:
  exact `c`-invariance under `tau` reparameterization.
- `Claim1lean/SmallKappaLipschitz.lean`:
  derivative-bound implies `O(κ)` increment inequality on `[0,κ]`.
- `Claim1lean/CovarianceDerivative.lean`:
  quotient-derivative identity in covariance form (`ω = N/Z` backbone).
- `Claim1lean/FiniteCovarianceBound.lean`:
  finite-support centered-product covariance inequality templates.
- `Claim1lean/RatioStateDerivativeBound.lean`:
  abstract `|∂ω|` bound from AN-7 + AN-8 ingredients.
- `Claim1lean/RatioStateIncrementBound.lean`:
  interval increment bound from derivative templates (`Cκ` control).
- `Claim1lean/FiniteExponentialFamilyDeriv.lean`:
  finite-sum exponential-family derivative bridge (`N'=-A`, `Z'=-B`).
- `Claim1lean/FiniteExponentialRepresentation.lean`:
  finite-sum centered representation bridge for \((A/Z)-\omega(B/Z)\).
- `Claim1lean/FiniteExponentialDerivativeBound.lean`:
  finite-sum model-internal derivative bounds for \(\omega=N/Z\).
- `Claim1lean/FiniteExponentialIncrementBound.lean`:
  finite-sum model-internal interval `Cκ` bound for \(\omega=N/Z\).
- `Claim1lean/WeightedLocalGraphDecay.lean`:
  weighted-local truncation, graph-decay operator, and denominator-rate ratio bounds.

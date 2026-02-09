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

## Relation to Current Claim 1 Queue

These formalizations support:

1. the \(c\)-invariance backbone used in AL/AP/AQ notes,
2. the AN-5 B5-prototype inequality pattern (small-\(\kappa\) Lipschitz step).

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
```

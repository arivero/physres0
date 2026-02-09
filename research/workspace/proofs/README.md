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
```

## Current formalized modules

- `Claim1lean/CInvariant.lean`:
  exact `c`-invariance under `tau` reparameterization.
- `Claim1lean/SmallKappaLipschitz.lean`:
  derivative-bound implies `O(κ)` increment inequality on `[0,κ]`.
- `Claim1lean/CovarianceDerivative.lean`:
  quotient-derivative identity in covariance form (`ω = N/Z` backbone).

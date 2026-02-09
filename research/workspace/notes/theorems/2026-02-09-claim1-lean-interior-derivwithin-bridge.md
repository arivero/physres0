# Claim 1 Phase AZ (AN-11): Lean Interior `derivWithin = deriv` Bridge

Date: 2026-02-09 (CET)  
Lean module: `research/workspace/proofs/Claim1lean/RatioStateIncrementBound.lean`

## Goal

Reduce AN-10 assumptions by proving the interior equality
`derivWithin = deriv` on `Ioo` and replacing the global `hwithin` hypothesis
with a boundary-aware variant.

## Formalized Additions (Lean)

The module now includes:

1. `derivWithin_Icc_eq_deriv_of_mem_Ioo`:
   \[
   t\in(0,\kappa)\ \Rightarrow\
   \mathrm{derivWithin}_{[0,\kappa]} f(t)=\mathrm{deriv}\,f(t).
   \]
2. `ratio_increment_bound_from_pointwise_deriv_with_boundary`:
   interval increment bound using:
   - interior pointwise `deriv` bound on `Ioo`,
   - one boundary `derivWithin` bound at \(t=0\).
3. `ratio_increment_bound_from_centered_avg_template_with_boundary`:
   AN-9 centered-average template plugged into the boundary-aware interval theorem.

## Why It Matters

This step reduces one of the heavier assumptions in AN-10:

1. no longer requires `derivWithin = deriv` on all of `Ico`,
2. uses a natural interior bridge and isolates boundary control explicitly.

## Build Check

```bash
cd research/workspace/proofs
/Users/arivero/.elan/bin/lake build Claim1lean.RatioStateIncrementBound
```

Build passes in current workspace.

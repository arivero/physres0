# Claim 1 Phase BA (AN-12): Lean One-Sided Boundary Bridge at \(t=0\)

Date: 2026-02-09 (CET)  
Lean module: `research/workspace/proofs/Claim1lean/RatioStateIncrementBound.lean`

## Goal

Reduce boundary assumptions in AN-11 by replacing the explicit
\([0,\kappa]\)-boundary derivative input with a one-sided \([0,\infty)\)-type input.

## Formalized Additions (Lean)

1. `derivWithin_Icc_zero_eq_derivWithin_Ici_zero` (for \(\kappa>0\)):
   \[
   \mathrm{derivWithin}_{[0,\kappa]} f(0)
   =
   \mathrm{derivWithin}_{[0,\infty)} f(0).
   \]
2. `ratio_increment_bound_from_centered_avg_template_oneSidedBoundary`:
   AN-11 interval bound now accepts one-sided boundary control at \(0\),
   then transfers it to the \([0,\kappa]\) interval theorem.

## Why It Matters

This is a concrete assumption reduction:

1. interior control still from AN-9 template on `Ioo`,
2. boundary control stated on `Ici` (right-neighborhood) rather than directly on `Icc`,
3. cleaner match with one-sided evolution setups at initial time.

## Build Check

```bash
cd research/workspace/proofs
/Users/arivero/.elan/bin/lake build Claim1lean.RatioStateIncrementBound
```

Build passes in current workspace.

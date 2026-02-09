# Claim 1 Phase AY (AN-10): Lean Ratio-State Interval Increment Bound

Date: 2026-02-09 (CET)  
Lean module: `research/workspace/proofs/Claim1lean/RatioStateIncrementBound.lean`

## Goal

Lift pointwise derivative control templates to interval increment bounds in a machine-checked way.

## Formalized Statements (Lean)

The module proves three bridge results:

1. `ratio_increment_bound_from_derivWithin`:
   from
   \[
   \|(\omega)'\_{\mathrm{within}}\|\le C \text{ on } (0,\kappa)
   \]
   derive
   \[
   |\omega(\kappa)-\omega(0)|\le C\kappa.
   \]
2. `ratio_increment_bound_from_pointwise_deriv`:
   same conclusion when `derivWithin = deriv` is supplied on interior points.
3. `ratio_increment_bound_from_centered_avg_template`:
   plugs AN-9 centered-average derivative template into the interval theorem, yielding
   \[
   |\omega(\kappa)-\omega(0)|
   \le
   |\alpha|\,K\,\mathrm{avg}(|g|)\,\kappa
   \]
   under the stated hypotheses.

## Why It Matters

This is the first Lean-checked end-to-end bridge from:

1. covariance-form derivative identity,
2. centered-product inequality,
3. small-interval increment bound,

matching the B5-style control shape used in the \(d=3\) bridge notes.

## Build Check

```bash
cd research/workspace/proofs
/Users/arivero/.elan/bin/lake build Claim1lean.RatioStateIncrementBound
```

Build passes in current workspace.

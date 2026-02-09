# Claim 1 Phase AW (AN-8): Lean Finite-Support Covariance Bound

Date: 2026-02-09 (CET)  
Lean module: `research/workspace/proofs/Claim1lean/FiniteCovarianceBound.lean`

## Goal

Provide a machine-checked finite-support inequality bridge from the AN-7
quotient-derivative identity toward explicit small-\(\kappa\) control templates.

## Formalized Statements (Lean)

For uniform finite averages
\[
\mathrm{avg}(h)=\frac1{n+1}\sum_{i=0}^n h_i,
\]
the module proves:

1. `abs_avg_le_avg_abs`:
   \[
   |\mathrm{avg}(h)|\le \mathrm{avg}(|h|).
   \]
2. `avg_centered_mul_le`:
   if \(|f_i-c|\le K\) for all \(i\), then
   \[
   \left|\mathrm{avg}\big((f-c)g\big)\right|
   \le
   K\,\mathrm{avg}(|g|).
   \]
3. `avg_centered_mul_le_twoM`:
   specialization to \(K=2M\).

## Why It Matters for Claim 1

This is the first Lean-checked covariance-style bound in a finite model.
It provides the inequality template needed after AN-7:

1. AN-7 gives a derivative/covariance-form identity,
2. AN-8 gives a rigorous finite-support control inequality on centered products,
3. next step is to combine both into a machine-checked derivative bound pipeline.

## Build Check

```bash
cd research/workspace/proofs
/Users/arivero/.elan/bin/lake build Claim1lean.FiniteCovarianceBound
```

Build passes in current workspace.

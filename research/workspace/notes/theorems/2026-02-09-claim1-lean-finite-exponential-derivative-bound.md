# Claim 1 Phase BE (AN-16): Lean Finite Exponential Derivative Bound

Date: 2026-02-09 (CET)  
Lean module: `research/workspace/proofs/Claim1lean/FiniteExponentialDerivativeBound.lean`

## Goal

Close the next Lean bridge by converting AN-14 (derivative hypotheses) + AN-15
(centered representation) into explicit model-internal derivative bounds for
the exponential-family ratio state.

## Machine-Checked Results

For
\[
\omega(\kappa)=\frac{N(\kappa)}{Z(\kappa)}
\]
in the finite exponential-family class:

1. `abs_deriv_omegaExp_le_weighted_abs`:
   \[
   |\omega'(\kappa)|
   \le
   \sum_i |p_i(\kappa)|\,|f_i-\omega(\kappa)|\,|s_i|.
   \]
2. `abs_deriv_omegaExp_le_centered_bound`:
   if \(|f_i-\omega(\kappa)|\le K\) for all \(i\), then
   \[
   |\omega'(\kappa)|
   \le
   K\sum_i |p_i(\kappa)|\,|s_i|.
   \]

## Why It Matters

This is the first machine-checked model-specific derivative-bound corollary that
does not require an externally supplied AN-9 representation hypothesis.
The bound is now derived internally from explicit finite exponential data.

## Build Check

```bash
cd research/workspace/proofs
/Users/arivero/.elan/bin/lake build Claim1lean.FiniteExponentialDerivativeBound
```

Build passes in current workspace.

# Claim 1 Phase BF (AN-17): Lean Finite Exponential Increment Bound

Date: 2026-02-09 (CET)  
Lean module: `research/workspace/proofs/Claim1lean/FiniteExponentialIncrementBound.lean`

## Goal

Lift the AN-16 model-internal derivative control into an AN-10-style
interval-increment theorem in the same finite exponential-family setting.

## Machine-Checked Result

`omegaExp_increment_bound_of_uniform_centered_control` proves:

\[
|\omega(\kappa)-\omega(0)| \le (K\,M)\,\kappa
\]

for \(\kappa\ge0\), under explicit assumptions on \([0,\kappa]\):

1. differentiability and `derivWithin = deriv` bridge,
2. non-vanishing partition channel \(Z(t)\neq0\),
3. uniform centered amplitude bound \(|f_i-\omega(t)|\le K\),
4. uniform weighted-moment bound
   \[
   \sum_i |p_i(t)|\,|s_i| \le M.
   \]

The proof is fully machine-checked by combining:

1. AN-10 interval bridge (`RatioStateIncrementBound.lean`),
2. AN-16 derivative bound (`FiniteExponentialDerivativeBound.lean`).

## Why It Matters

This gives a concrete finite-model `Cκ` increment theorem in the same shape as
the B5 target, now entirely inside the finite exponential-family formal chain.

## Build Check

```bash
cd research/workspace/proofs
/Users/arivero/.elan/bin/lake build Claim1lean.FiniteExponentialIncrementBound
```

Build passes in current workspace.

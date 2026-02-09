# Claim 1 Phase BF/BG1 (AN-17/AN-18): Lean Finite Exponential Increment Bound

Date: 2026-02-09 (CET)  
Lean module: `research/workspace/proofs/Claim1lean/FiniteExponentialIncrementBound.lean`

## Goal

Lift the AN-16 model-internal derivative control into an AN-10-style
interval-increment theorem in the same finite exponential-family setting, then
reduce its regularity side-assumptions using AN-18 automatic-regularity lemmas.

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

AN-18 adds `omegaExp_increment_bound_of_uniform_centered_control_auto`, which
derives the BF regularity assumptions automatically from finite-model structure:

1. `Zsum(t) > 0` and `Zsum(t) ≠ 0`,
2. global differentiability of `Nsum/Zsum`,
3. interval bridge `derivWithin = deriv` on `Icc(0,κ)` for `κ>0`.

After this reduction, only nonnegativity and the centered/moment control
hypotheses remain explicit.

## Why It Matters

This gives a concrete finite-model `Cκ` increment theorem in the same shape as
the B5 target, now entirely inside the finite exponential-family formal chain,
with AN-18 removing manual regularity bookkeeping.

## Build Check

```bash
cd research/workspace/proofs
/Users/arivero/.elan/bin/lake build Claim1lean.FiniteExponentialIncrementBound
/Users/arivero/.elan/bin/lake build Claim1lean.FiniteExponentialRegularity
```

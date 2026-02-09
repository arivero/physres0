# Claim 1 Phase BC (AN-14): Lean Finite Exponential Derivative Bridge

Date: 2026-02-09 (CET)  
Lean module: `research/workspace/proofs/Claim1lean/FiniteExponentialFamilyDeriv.lean`

## Goal

Formalize a concrete finite-dimensional parameter-differentiation bridge that
supplies AN-7 derivative hypotheses from an explicit model class.

## Formalized Objects

For finite index set `Fin (n+1)` and real data \(s_i,f_i\):

1. numerator channel
   \[
   N(\kappa)=\sum_i e^{-\kappa s_i}f_i,
   \]
2. denominator channel
   \[
   Z(\kappa)=\sum_i e^{-\kappa s_i},
   \]
3. insertion channels
   \[
   A(\kappa)=\sum_i e^{-\kappa s_i}(s_i f_i),\qquad
   B(\kappa)=\sum_i e^{-\kappa s_i}s_i.
   \]

## Machine-Checked Derivative Results

The module proves:

1. `hasDerivAt_Nsum`:
   \[
   N'(\kappa)=-A(\kappa),
   \]
2. `hasDerivAt_Zsum`:
   \[
   Z'(\kappa)=-B(\kappa).
   \]

These are exactly the derivative-structure assumptions used abstractly in AN-7.

## Intriguing Observation (Saved for Future Search)

The finite exponential family shows that the covariance-template derivative
assumptions are not abstract artifacts: they are automatic in explicit
Boltzmann-type weighted finite models.  
This is a promising bridge candidate for a later integral-level generalization.

## Build Check

```bash
cd research/workspace/proofs
/Users/arivero/.elan/bin/lake build Claim1lean.FiniteExponentialFamilyDeriv
```

Build passes in current workspace.

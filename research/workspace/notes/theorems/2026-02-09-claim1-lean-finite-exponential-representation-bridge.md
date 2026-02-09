# Claim 1 Phase BD (AN-15): Lean Finite Exponential Representation Bridge

Date: 2026-02-09 (CET)  
Lean module: `research/workspace/proofs/Claim1lean/FiniteExponentialRepresentation.lean`

## Goal

Discharge the AN-13 missing representation ingredient by deriving a centered
covariance-form representation directly from explicit finite exponential-family
data.

## Formalized Objects

For finite index set `Fin (n+1)`:

1. ratio-state observable
   \[
   \omega(\kappa)=\frac{N(\kappa)}{Z(\kappa)},
   \]
   formalized as `omegaExp`.
2. normalized exponential weight
   \[
   p_i(\kappa)=\frac{e^{-\kappa s_i}}{Z(\kappa)},
   \]
   formalized as `pExp`.

## Machine-Checked Results

1. `centered_weighted_sum_eq`:
   \[
   \sum_i e^{-\kappa s_i}\,(f_i-\omega(\kappa))\,s_i
   =
   A(\kappa)-\omega(\kappa)\,B(\kappa).
   \]
2. `covariance_repr_weighted_exp`:
   \[
   \frac{A}{Z}-\omega\frac{B}{Z}
   =
   \frac{1}{Z}\sum_i e^{-\kappa s_i}\,(f_i-\omega)\,s_i.
   \]
3. `covariance_repr_weighted_prob`:
   \[
   \frac{A}{Z}-\omega\frac{B}{Z}
   =
   \sum_i p_i(\kappa)\,(f_i-\omega)\,s_i.
   \]

This is the machine-checked centered representation bridge from concrete model
assumptions to the AN-7 covariance term.

## Why It Matters

AN-14 provided derivative-shape hypotheses (`N'=-A`, `Z'=-B`) from explicit
finite models. AN-15 now provides the missing representation side for the same
model class, reducing the gap between concrete assumptions and the AN-9/AN-10
bound pipeline.

## Build Check

```bash
cd research/workspace/proofs
/Users/arivero/.elan/bin/lake build Claim1lean.FiniteExponentialRepresentation
```

Build passes in current workspace.

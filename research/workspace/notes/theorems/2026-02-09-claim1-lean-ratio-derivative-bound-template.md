# Claim 1 Phase AX (AN-9): Lean Ratio-Derivative Bound Template

Date: 2026-02-09 (CET)  
Lean module: `research/workspace/proofs/Claim1lean/RatioStateDerivativeBound.lean`

## Goal

Combine the Lean AN-7 and AN-8 ingredients into one machine-checked
`|∂ω|` bound template for ratio states.

## Formalized Statement (Lean)

Given:

1. quotient state \(\omega = N/Z\),
2. derivative data \(N'(x)=-\alpha A(x)\), \(Z'(x)=-\alpha B(x)\), \(Z(x)\neq0\),
3. representation
   \[
   \frac{A(x)}{Z(x)}-\frac{N(x)}{Z(x)}\frac{B(x)}{Z(x)}
   =
   \mathrm{avg}\big((f-c)g\big),
   \]
4. pointwise bound \(|f_i-c|\le K\),

the Lean theorem proves:
\[
\left|\frac{d}{dx}\left(\frac{N}{Z}\right)(x)\right|
\le
|\alpha|\,K\,\mathrm{avg}(|g|).
\]

## Dependency Chain (Machine-Checked)

1. AN-7 (`CovarianceDerivative.lean`): quotient derivative covariance form.
2. AN-8 (`FiniteCovarianceBound.lean`): centered-product average bound.
3. AN-9 (`RatioStateDerivativeBound.lean`): combined derivative-bound template.

## Why It Matters

This is the first Lean-checked template that directly mirrors the B5-style
small-\(\kappa\) control logic at the derivative level.

## Build Check

```bash
cd research/workspace/proofs
/Users/arivero/.elan/bin/lake build Claim1lean.RatioStateDerivativeBound
```

Build passes in current workspace.

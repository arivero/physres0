# Claim 1 Phase AV (AN-7): Lean Covariance-Derivative Bridge Lemma

Date: 2026-02-09 (CET)  
Lean module: `research/workspace/proofs/Claim1lean/CovarianceDerivative.lean`

## Goal

Push Lean formalization one step beyond algebraic \(c\)-invariance and interval Lipschitz:
formalize the quotient-derivative identity that underlies covariance-type evolution formulas in AN-5.

## Formalized Statement (Lean)

For real-valued functions \(N,Z,A,B\), scalar \(\alpha\), and point \(x\), if

1. \(Z(x)\neq 0\),
2. \(N'(x)=-\alpha A(x)\),
3. \(Z'(x)=-\alpha B(x)\),

then
\[
\frac{d}{dx}\Big(\frac{N}{Z}\Big)(x)
=
(-\alpha)\left(\frac{A(x)}{Z(x)}-\frac{N(x)}{Z(x)}\frac{B(x)}{Z(x)}\right),
\]
with an equivalent factored form
\[
\frac{d}{dx}\Big(\frac{N}{Z}\Big)(x)
=
\frac{-\alpha}{Z(x)}
\left(A(x)-\frac{N(x)}{Z(x)}B(x)\right).
\]

## Why It Matters for Claim 1

This is the exact algebraic backbone of the
\[
\partial_\kappa \omega_\kappa(F)\sim -\text{const}\cdot \mathrm{Cov}(F,G)
\]
pattern used in the small-\(\kappa\) bridge arguments:

1. `N` = unnormalized inserted integral,
2. `Z` = partition factor,
3. ratio derivative + quotient rule = covariance-shape identity.

## Build Check

```bash
cd research/workspace/proofs
/Users/arivero/.elan/bin/lake build Claim1lean.CovarianceDerivative
```

Build passes in current workspace.

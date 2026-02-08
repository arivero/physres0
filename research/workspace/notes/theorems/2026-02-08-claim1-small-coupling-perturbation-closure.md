# Claim 1 Phase I: Small-Coupling Polynomial Perturbation Closure

Date: 2026-02-08  
Depends on: `research/workspace/notes/theorems/2026-02-08-claim1-gaussian-h1-h6-closure.md`

## Purpose

Extend the Claim 1 continuum closure beyond the pure Gaussian core to a controlled interacting family with explicit small-coupling bounds.

## Regularized Oscillatory Model

Fix \(\varepsilon>0\), \(\eta>0\), and sequences
\[
0<\lambda_-\le \lambda_j\le \lambda_+,\qquad
0\le \kappa_j\le \kappa_+.
\]
For \(X_N=\mathbb R^N\), define
\[
S_N^{(g)}(x)=\frac12\sum_{j=1}^N\lambda_jx_j^2+g\sum_{j=1}^N\kappa_jx_j^4.
\]
Use the convergent complex weight
\[
W_{\varepsilon,\eta,N}^{(g)}(x)
:=
\exp\!\left[-(\eta-i/\varepsilon)\,S_N^{(g)}(x)\right].
\]

For cylinder observable \(F_m\in C_b^2(\mathbb R^m)\), \(N\ge m\),
\[
\omega_{\varepsilon,\eta,N}^{(g)}(F_m)
:=
\frac{\int_{\mathbb R^N}W_{\varepsilon,\eta,N}^{(g)}(x)\,F_m(x_1,\dots,x_m)\,dx}
{\int_{\mathbb R^N}W_{\varepsilon,\eta,N}^{(g)}(x)\,dx}.
\]

## Theorem 1 (Exact \(N\)-Stability for Product Interactions)

For every fixed \(g\), \(\varepsilon\), \(\eta\), and cylinder \(F_m\),
\[
\omega_{\varepsilon,\eta,N}^{(g)}(F_m)=\omega_{\varepsilon,\eta,m}^{(g)}(F_m),
\qquad N\ge m.
\]

Proof:

1. The action is coordinate-factorized (\(x_j\)-independent blocks), so numerator and denominator split into products.
2. Tail factors \(j>m\) cancel exactly in the normalized ratio.
3. The remaining expression is the \(m\)-dimensional one.

So H1 and H6 hold exactly in this class, and H2-H3 hold from \(\eta>0\) plus uniform quadratic coercivity.

## Theorem 2 (Small-Coupling Lipschitz Control)

Let \(V_N(x):=\sum_{j=1}^N\kappa_jx_j^4\).  
For fixed \(m\), define \(\omega^{(g)}:=\omega_{\varepsilon,\eta,m}^{(g)}\). Then
\[
\frac{d}{dg}\,\omega^{(g)}(F_m)
=
-(\eta-i/\varepsilon)\,
\mathrm{Cov}_{\omega^{(g)}}(F_m,V_m),
\]
where \(V_m:=\sum_{j=1}^m\kappa_jx_j^4\).

Hence for \(|g|\le g_0\),
\[
|\omega^{(g)}(F_m)-\omega^{(0)}(F_m)|
\le
|g|\,|\eta-i/\varepsilon|\,\sup_{|s|\le g_0}
|\mathrm{Cov}_{\omega^{(s)}}(F_m,V_m)|.
\]
Using \(|\mathrm{Cov}(F,V_m)|\le 2\|F_m\|_\infty\,\mathbb E_{\omega^{(s)}}|V_m|\), obtain
\[
|\omega^{(g)}(F_m)-\omega^{(0)}(F_m)|
\le
C_m(\varepsilon,\eta,g_0)\,\|F_m\|_\infty\,|g|.
\]

This gives explicit \(O(g)\) stability around the Gaussian closure.

## Corollary (Claim 1 Continuum Skeleton Upgrade)

Within this regularized interacting class:

1. H1-H3, H5-H6 are closed exactly/constructively.
2. H4 is explicit by coefficient-level counterterm repair (as in Phase H).
3. Interaction dependence is controlled by a Lipschitz perturbation bound.

So Claim 1 closure now extends from Gaussian core to a small-coupling polynomial neighborhood (with \(\eta>0\) regulator).

## Remaining Gap

Remove the \(\eta>0\) regulator and keep uniform control as \(\eta\to0^+\), while preserving the same cylinder-limit and channel statements.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_small_coupling_perturbation_check.py
```

The script numerically checks:

1. \(N\)-stability for a cylinder observable under quartic product interaction.
2. Near-linear \(O(g)\) response around \(g=0\) in the regularized model.

# Claim 1 Phase P: Observable-Class Extension to Schwartz and Weighted Sobolev Classes

Date: 2026-02-09  
Depends on: `research/workspace/notes/theorems/2026-02-09-claim1-partition-nonvanishing-bounds.md`

## Goal

Upgrade Claim 1 beyond Gaussian-exponential cylinders to larger dense observable classes with explicit continuity bounds.

## Setup

Consider a finite-dimensional de-regularized branch (\(\eta\to0^+\) already taken) represented on a rotated contour:
\[
\mathcal I(F):=
\int_{\mathbb R^d} e^{i\Phi(y)}\,W(y)\,F(Ay)\,dy,
\]
where:

1. \(A\in GL(d,\mathbb C)\) is fixed linear (e.g. contour rotation),
2. \(|W(y)|\le C_0 e^{-c_4\|y\|^4+c_2\|y\|^2}\) with \(c_4>0\),
3. normalized state is \(\omega(F)=\mathcal I(F)/\mathcal I(1)\), assuming \(\mathcal I(1)\neq0\).

This covers the quartic-stabilized de-regularized constructions from prior phases.

## Theorem 1 (Schwartz Continuity)

For any integer \(k>d\), there exists \(C_k>0\) such that
\[
|\mathcal I(F)|
\le
C_k\sup_{x\in\mathbb R^d}(1+\|x\|)^k|F(x)|
\qquad(F\in\mathcal S(\mathbb R^d)).
\]
Hence \(\mathcal I\) is continuous on \(\mathcal S(\mathbb R^d)\), and so is \(\omega\).

### Proof

Using the weight bound and \(\|Ay\|\le \|A\|\,\|y\|\):
\[
|F(Ay)|\le \sup_x (1+\|x\|)^k|F(x)|\,(1+\|Ay\|)^{-k}
\le
C_A\,p_k(F)\,(1+\|y\|)^{-k},
\]
where \(p_k(F):=\sup_x (1+\|x\|)^k|F(x)|\). Therefore
\[
|\mathcal I(F)|
\le
C_0C_A\,p_k(F)\int_{\mathbb R^d}
e^{-c_4\|y\|^4+c_2\|y\|^2}(1+\|y\|)^{-k}\,dy.
\]
The integral is finite. \(\square\)

## Theorem 2 (Weighted Sobolev Bound)

For \(k>d/2\), define
\[
\|F\|_{H^{0,k}}
:=
\left\|(1+\|x\|^2)^{k/2}F(x)\right\|_{L^2(\mathbb R^d)}.
\]
Then there exists \(C_k'>0\) such that
\[
|\mathcal I(F)|\le C_k'\,\|F\|_{H^{0,k}}.
\]

### Proof

By Cauchy-Schwarz:
\[
|\mathcal I(F)|
\le
\left\|W(\cdot)(1+\|\cdot\|^2)^{-k/2}\right\|_{L^2}
\left\|(1+\|y\|^2)^{k/2}F(Ay)\right\|_{L^2_y}.
\]
The first factor is finite from quartic decay.
For the second, linear change of variables gives
\[
\left\|(1+\|y\|^2)^{k/2}F(Ay)\right\|_{L^2_y}
\le
C_A'\|F\|_{H^{0,k}}.
\]
\(\square\)

## Density Step (Gaussian-Exponential to Schwartz)

Let
\[
\mathcal G:=\mathrm{span}\{p(x)e^{-x^\top Bx}: p\ \text{polynomial},\ B\succ0\}.
\]
Using Hermite basis representation (after linear normalization of \(B\)), finite Hermite sums are dense in \(\mathcal S(\mathbb R^d)\).
Therefore \(\mathcal G\) is dense in \(\mathcal S\), and by Theorem 1 the functional \(\mathcal I\) extends uniquely from \(\mathcal G\) to all Schwartz observables.

## Corollary (Claim 1 Observable Upgrade)

Claim 1 de-regularized finite-dimensional branches now act continuously on:

1. \(\mathcal S(\mathbb R^d)\),
2. weighted Sobolev spaces \(H^{0,k}\) for \(k>d/2\),

not only on Gaussian-exponential test families.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_observable_density_hermite_check.py
```

The script demonstrates convergence of \(\omega(F_N)\to\omega(F)\) for a Schwartz target \(F\), where \(F_N\) are polynomial-Gaussian truncations (equivalently finite combinations in the same dense Hermite-Gaussian span).

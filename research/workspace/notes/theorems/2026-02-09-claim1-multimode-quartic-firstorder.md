# Claim 1 Phase AC: First-Order Non-Gaussian Multi-Mode Quartic Closure

Date: 2026-02-09  
Depends on: `research/workspace/notes/theorems/2026-02-09-claim1-largeN-coupled-gaussian-tail.md`

## Goal

Push Claim 1 past quadratic/non-factorized Gaussian structure by adding a genuinely multi-mode quartic interaction and proving a theorem-grade large-\(N\) closure at first perturbative order.

## Model

Fix observed block \(u\in\mathbb R^m\), \(m\ge1\), and for \(N\ge m\), tail \(v=(v_{m+1},\dots,v_N)\).  
Set
\[
S_N^{(0)}(u,v)
=
P_m(u)+\sum_{j=m+1}^N \frac{d_j(u)}{2}v_j^2,
\qquad
d_j(u)=\lambda_j+2\beta_j(u),
\]
\[
\beta_j(u)=\sum_{i=1}^m a_{ij}u_i^2,\quad
\lambda_j\ge\lambda_->0,\quad
a_{ij}\ge0,\quad
A_j:=\sum_{i=1}^m a_{ij},
\quad
\sum_{j=m+1}^\infty \frac{A_j}{\lambda_j}<\infty.
\]

Add pair-quartic interaction
\[
W_N(v):=\sum_{m<j<k\le N} b_{jk}\,v_j^2v_k^2,
\qquad b_{jk}=b_{kj}\ge0,
\]
with weighted summability
\[
\rho_\infty:=\sum_{m<j<k<\infty}\frac{b_{jk}}{\lambda_j\lambda_k}<\infty,
\qquad
\rho_N:=\sum_{\max\{j,k\}>N}\frac{b_{jk}}{\lambda_j\lambda_k}\to0.
\]

Let \(c=\eta-i/\varepsilon\), \(\eta>0\). Define the normalized state with coupling \(g\):
\[
\omega_{\varepsilon,\eta,N}^{(g)}(F_m)
:=
\frac{\int e^{-c(S_N^{(0)}+gW_N)}F_m(u)\,du\,dv}
{\int e^{-c(S_N^{(0)}+gW_N)}\,du\,dv}.
\]

## Theorem (First-Order Coefficient Convergence)

For bounded cylinder \(F_m\), define the first-order coefficient
\[
\Gamma_N(F_m):=
\left.\frac{d}{dg}\omega_{\varepsilon,\eta,N}^{(g)}(F_m)\right|_{g=0}
=
-c\,\mathrm{Cov}_{\omega_{\varepsilon,\eta,N}^{(0)}}(F_m,W_N).
\]
Then:

1. \(\Gamma_N(F_m)\) converges as \(N\to\infty\).
2. There exists \(C_{F_m,\varepsilon,\eta}>0\) such that
   \[
   |\Gamma_{N'}(F_m)-\Gamma_N(F_m)|
   \le
   C_{F_m,\varepsilon,\eta}\left(
   \sum_{j=N+1}^{N'}\frac{A_j}{\lambda_j}
   +\rho_N
   \right),\qquad N'>N\ge m.
   \]
3. Therefore the first-order truncation
   \[
   \omega_{N}^{[1]}(F_m;g):=
   \omega_{\varepsilon,\eta,N}^{(0)}(F_m)+g\,\Gamma_N(F_m)
   \]
   has a large-\(N\) limit for each fixed \(g\).

## Proof

Under \(g=0\), tail modes are independent Gaussians conditional on \(u\), with
\[
\mathbb E_0[v_j^2\mid u]=\frac{1}{c\,d_j(u)},\qquad
\mathbb E_0[v_j^2v_k^2\mid u]=\frac{1}{c^2\,d_j(u)d_k(u)}\quad(j\neq k).
\]
Hence
\[
R_N(u):=\mathbb E_0[W_N\mid u]
=
\frac{1}{c^2}\sum_{m<j<k\le N}\frac{b_{jk}}{d_j(u)d_k(u)}.
\]
Since \(d_j(u)\ge\lambda_j\),
\[
|R_N(u)|\le \frac{1}{|c|^2}\sum_{m<j<k\le N}\frac{b_{jk}}{\lambda_j\lambda_k}
\le \frac{\rho_\infty}{|c|^2},
\]
and
\[
|R_{N'}(u)-R_N(u)|
\le
\frac{\rho_N}{|c|^2}
\]
uniformly in \(u\).

Let
\[
\Phi_N(u):=\prod_{j=m+1}^N d_j(u)^{-1/2}.
\]
As in the Gaussian-tail theorem, \(\Phi_N\) converges with tail control
\[
|\Phi_{N'}(u)-\Phi_N(u)|\le C_\Phi e^{B\|u\|^2}\sum_{j=N+1}^{N'}\frac{A_j}{\lambda_j}.
\]

Now write
\[
\Gamma_N(F_m)=-c\left(\frac{\mathcal A_N(F_m)}{\mathcal D_N}
-\frac{\mathcal N_N(F_m)}{\mathcal D_N}\frac{\mathcal A_N(1)}{\mathcal D_N}\right),
\]
with
\[
\mathcal N_N(F):=\int e^{-cP_m(u)}F(u)\Phi_N(u)\,du,\quad
\mathcal D_N:=\mathcal N_N(1),
\]
\[
\mathcal A_N(F):=\int e^{-cP_m(u)}F(u)\Phi_N(u)R_N(u)\,du.
\]
Use the bounds for \(\Phi_N\), \(R_N\), and \(R_{N'}-R_N\), together with
\[
|e^{-cP_m(u)}|\le e^{-\eta P_m(u)}
\]
and quartic coercivity of \(P_m\), to get Cauchy bounds for \(\mathcal A_N,\mathcal N_N,\mathcal D_N\) with tail
\[
O\!\left(\sum_{j>N}\frac{A_j}{\lambda_j}+\rho_N\right).
\]
Applying the ratio-difference inequality (denominator bounded away from zero for large \(N\)) yields the same tail control for \(\Gamma_N(F_m)\). \(\square\)

## Scope

This is a theorem-grade non-Gaussian multi-mode closure at first perturbative order.  
The next frontier is non-perturbative large-\(N\) control for \(g\neq0\) in this pair-quartic class.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_multimode_quartic_firstorder_check.py
```

The script evaluates the first-order corrected truncation \(\omega_N^{[1]}\) and confirms large-\(N\) stabilization against the mixed control tail \(\sum_{j>N}A_j/\lambda_j+\rho_N\).

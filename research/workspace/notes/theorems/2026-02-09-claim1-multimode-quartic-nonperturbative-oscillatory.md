# Claim 1 Phase AE: Non-Perturbative Multi-Mode Quartic Control in Oscillatory Regularization

Date: 2026-02-09  
Depends on: `research/workspace/notes/theorems/2026-02-09-claim1-multimode-quartic-nonperturbative-euclidean.md`

## Goal

Extend finite-\(g\) non-perturbative large-\(N\) control of the multi-mode quartic sector from Euclidean regularization (\(c=\eta\)) to oscillatory regularization \(c=\eta-i/\varepsilon\), \(\eta>0\).

## Model

Use the same model as Phase AD:
\[
S_N^{(0)}(u,v)=P_m(u)+\sum_{j=m+1}^N \frac{d_j(u)}{2}v_j^2,
\quad
d_j(u)=\lambda_j+2\beta_j(u),
\]
\[
\beta_j(u)=\sum_{i=1}^m a_{ij}u_i^2,\quad
\lambda_j\ge\lambda_->0,\quad
\sum_{j>m}\frac{A_j}{\lambda_j}<\infty,\ \ A_j=\sum_i a_{ij},
\]
\[
W_N(v)=\sum_{m<j<k\le N} b_{jk}v_j^2v_k^2,\quad b_{jk}\ge0,\quad
\rho_\infty:=\sum_{m<j<k<\infty}\frac{b_{jk}}{\lambda_j\lambda_k}<\infty.
\]

Define
\[
\rho_N:=\sum_{\max\{j,k\}>N}\frac{b_{jk}}{\lambda_j\lambda_k}\to0.
\]

For \(c=\eta-i/\varepsilon\) (\(\eta>0\)), \(g\ge0\),
\[
\omega_{c,N}^{(g)}(F_m)
:=
\frac{\int e^{-c(S_N^{(0)}+gW_N)}F_m(u)\,du\,dv}
{\int e^{-c(S_N^{(0)}+gW_N)}\,du\,dv}.
\]

## Theorem (Finite-\(g\) Oscillatory Large-\(N\) Convergence)

For every bounded cylinder \(F_m\):

1. \(\omega_{c,N}^{(g)}(F_m)\) converges as \(N\to\infty\), provided the limiting denominator is nonzero.
2. There exists \(C_{F_m,c,g}>0\) such that for \(N'>N\ge m\),
   \[
   |\omega_{c,N'}^{(g)}(F_m)-\omega_{c,N}^{(g)}(F_m)|
   \le
   C_{F_m,c,g}
   \left(
   \sum_{j=N+1}^{N'}\frac{A_j}{\lambda_j}
   +\rho_N
   \right).
   \]

## Proof

Choose the principal branch \(\sqrt c\) (\(\Re \sqrt c>0\)), and in the tail variables set
\[
y_j=\sqrt c\,v_j,\qquad v_j=\frac{y_j}{\sqrt c}.
\]
Since the integrand is entire in each tail variable and \(\eta>0\) provides sector decay, contour rotation/scaling to \(\mathbb R^{N-m}\) is valid.
Then
\[
c\frac{d_j}{2}v_j^2=\frac{d_j}{2}y_j^2,\qquad
cg\,v_j^2v_k^2=\frac{g}{c}\,y_j^2y_k^2.
\]
Up to \(u\)-independent Jacobian factors (cancelled in normalized ratios), the tail factor is
\[
\exp\!\left(
-\sum_{j=m+1}^N\frac{d_j(u)}{2}y_j^2
-\frac{g}{c}W_N(y)
\right).
\]
Define
\[
\kappa:=\frac{g}{c},\qquad \Re\kappa=\frac{g\eta}{|c|^2}\ge0.
\]
Hence
\[
|e^{-\kappa W_N}|\le e^{-\Re\kappa\,W_N}\le1.
\]

So
\[
\omega_{c,N}^{(g)}(F_m)
=
\frac{\int_{\R^m}e^{-cP_m(u)}F_m(u)\Phi_N(u)R_N(u;\kappa)\,du}
{\int_{\R^m}e^{-cP_m(u)}\Phi_N(u)R_N(u;\kappa)\,du},
\]
with
\[
\Phi_N(u)=\prod_{j=m+1}^N d_j(u)^{-1/2},
\]
\[
R_N(u;\kappa):=\mathbb E_{\nu_{N,u}}\!\left[e^{-\kappa W_N}\right],
\]
where \(\nu_{N,u}\) is the real Gaussian product law
\[
\nu_{N,u}=\bigotimes_{j=m+1}^N\mathcal N\!\left(0,\frac{1}{d_j(u)}\right).
\]

As in Phase AD,
\[
|R_{N'}(u;\kappa)-R_N(u;\kappa)|
\le
|\kappa|\,\mathbb E_{\nu_{N',u}}|W_{N'}-W_N|
\le
|\kappa|\,\rho_N
\]
uniformly in \(u\), since \(d_j(u)\ge\lambda_j\).

Also \(\Phi_N\) has the same Gaussian-tail Cauchy control:
\[
|\Phi_{N'}-\Phi_N|
\le
C_\Phi e^{B\|u\|^2}\sum_{j=N+1}^{N'}\frac{A_j}{\lambda_j}.
\]
Thus
\[
|\Phi_{N'}R_{N'}-\Phi_NR_N|
\le
C_1e^{B\|u\|^2}
\left(
\sum_{j=N+1}^{N'}\frac{A_j}{\lambda_j}
+\rho_N
\right).
\]
Multiplying by \(|e^{-cP_m(u)}|=e^{-\eta P_m(u)}\) gives an integrable dominant envelope (quartic coercivity).
Dominated convergence and the quotient-difference bound yield the claimed convergence and rate. \(\square\)

## Scope

This closes finite-\(g\) non-perturbative large-\(N\) control for the multi-mode quartic class directly in oscillatory regularization (\(\eta>0\)).

Open frontier: de-regularization \(\eta\to0^+\) for this non-perturbative multi-mode quartic sector with uniform-in-\(N\) control.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_multimode_quartic_nonperturbative_oscillatory_check.py
```

The script estimates \(\omega_{c,N}^{(g)}(F_m)\) (complex-valued) with Monte Carlo inner expectation and confirms stabilization with the same mixed-tail control.

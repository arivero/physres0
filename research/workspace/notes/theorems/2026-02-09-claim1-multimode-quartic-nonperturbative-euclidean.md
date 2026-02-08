# Claim 1 Phase AD: Non-Perturbative Multi-Mode Quartic Control (Euclidean Sector)

Date: 2026-02-09  
Depends on: `research/workspace/notes/theorems/2026-02-09-claim1-multimode-quartic-firstorder.md`

## Goal

Upgrade the multi-mode quartic sector from first-order perturbative control to finite-\(g\) non-perturbative large-\(N\) convergence in the regularized Euclidean sector (\(c=\eta>0\)).

## Model

Fix \(m\ge1\), \(u\in\mathbb R^m\), \(N\ge m\), and
\[
S_N^{(0)}(u,v)=P_m(u)+\sum_{j=m+1}^N \frac{d_j(u)}{2}v_j^2,
\qquad
d_j(u)=\lambda_j+2\beta_j(u),
\]
\[
\beta_j(u)=\sum_{i=1}^m a_{ij}u_i^2,\quad
\lambda_j\ge\lambda_->0,\quad
a_{ij}\ge0,\quad
\sum_{j=m+1}^\infty \frac{A_j}{\lambda_j}<\infty,\ \ A_j=\sum_i a_{ij}.
\]

Pair-quartic interaction:
\[
W_N(v)=\sum_{m<j<k\le N} b_{jk}\,v_j^2v_k^2,\qquad b_{jk}=b_{kj}\ge0.
\]
Assume weighted summability
\[
\rho_\infty:=\sum_{m<j<k<\infty}\frac{b_{jk}}{\lambda_j\lambda_k}<\infty,
\qquad
\rho_N:=\sum_{\max\{j,k\}>N}\frac{b_{jk}}{\lambda_j\lambda_k}\to0.
\]

For \(\eta>0\), \(g\ge0\), define
\[
\omega_{\eta,N}^{(g)}(F_m)
:=
\frac{\int e^{-\eta(S_N^{(0)}+gW_N)}F_m(u)\,du\,dv}
{\int e^{-\eta(S_N^{(0)}+gW_N)}\,du\,dv}.
\]

## Theorem (Finite-\(g\) Large-\(N\) Convergence)

For every bounded cylinder observable \(F_m\):

1. \(\omega_{\eta,N}^{(g)}(F_m)\) converges as \(N\to\infty\) for each fixed \(g\ge0\), provided the limiting denominator is nonzero.
2. There exists \(C_{F_m,\eta,g}>0\) such that for \(N'>N\ge m\),
   \[
   |\omega_{\eta,N'}^{(g)}(F_m)-\omega_{\eta,N}^{(g)}(F_m)|
   \le
   C_{F_m,\eta,g}
   \left(
   \sum_{j=N+1}^{N'}\frac{A_j}{\lambda_j}
   +\rho_N
   \right).
   \]

So the non-perturbative rate keeps the same mixed-tail structure as the first-order theorem.

## Proof

Integrating Gaussians conditionally on \(u\), write
\[
\omega_{\eta,N}^{(g)}(F_m)
=
\frac{\int_{\mathbb R^m}e^{-\eta P_m(u)}F_m(u)\Phi_N(u)R_N(u;g)\,du}
{\int_{\mathbb R^m}e^{-\eta P_m(u)}\Phi_N(u)R_N(u;g)\,du},
\]
where
\[
\Phi_N(u)=\prod_{j=m+1}^N d_j(u)^{-1/2},
\]
and \(R_N(u;g)\) is the expectation
\[
R_N(u;g):=
\mathbb E_{\mu_{N,u}}\!\left[e^{-\eta gW_N}\right],
\]
for the product Gaussian law
\[
\mu_{N,u}=\bigotimes_{j=m+1}^N
\mathcal N\!\left(0,\frac{1}{\eta d_j(u)}\right).
\]

Because \(W_N\ge0\), \(0\le e^{-\eta gW_N}\le1\), hence
\[
0<R_N(u;g)\le1.
\]

For \(N'>N\), use \(|e^{-x}-e^{-y}|\le|x-y|\) on \([0,\infty)\):
\[
|R_{N'}(u;g)-R_N(u;g)|
\le
\eta g\,\mathbb E_{\mu_{N',u}}|W_{N'}-W_N|.
\]
Since terms are nonnegative and independent moments factor,
\[
\mathbb E_{\mu_{N',u}}(W_{N'}-W_N)
=
\frac{1}{\eta^2}
\sum_{\max\{j,k\}>N}\frac{b_{jk}}{d_j(u)d_k(u)}
\le
\frac{\rho_N}{\eta^2}.
\]
Therefore
\[
|R_{N'}(u;g)-R_N(u;g)|
\le
\frac{g}{\eta}\rho_N
\]
uniformly in \(u\), so \(R_N(\cdot;g)\) is uniformly Cauchy.

For \(\Phi_N\), the Gaussian-tail theorem gives
\[
|\Phi_{N'}(u)-\Phi_N(u)|
\le
C_\Phi e^{B\|u\|^2}\sum_{j=N+1}^{N'}\frac{A_j}{\lambda_j}.
\]
Combining
\[
\Phi_{N'}R_{N'}-\Phi_NR_N
=
(\Phi_{N'}-\Phi_N)R_{N'}+\Phi_N(R_{N'}-R_N),
\]
and \(0<R_N\le1\), we obtain
\[
|\Phi_{N'}(u)R_{N'}(u;g)-\Phi_N(u)R_N(u;g)|
\le
C_1e^{B\|u\|^2}
\left(
\sum_{j=N+1}^{N'}\frac{A_j}{\lambda_j}
+\rho_N
\right).
\]
Multiplying by \(e^{-\eta P_m(u)}\) yields an integrable envelope by quartic coercivity.
Thus numerator and denominator are Cauchy with the same tail, and the normalized ratio estimate follows via the standard quotient-difference inequality (denominator bounded away from zero for large \(N\)). \(\square\)

## Scope

This closes the finite-\(g\) (non-perturbative) branch for the multi-mode quartic family in the Euclidean regularized sector.

Remaining step: extend this finite-\(g\) control to oscillatory \(c=\eta-i/\varepsilon\) without losing large-\(N\) uniformity.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_multimode_quartic_nonperturbative_euclidean_check.py
```

The script estimates \(\omega_{\eta,N}^{(g)}(F_m)\) for increasing \(N\) (Monte Carlo inner expectation for \(R_N\)) and compares successive differences against the mixed control tail.

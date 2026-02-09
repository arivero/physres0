# Claim 1 Phase AG: De-Regularization \(\eta\to0^+\) for Finite-\(g\) Multi-Mode Quartic Sector

Date: 2026-02-09  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-multimode-quartic-nonperturbative-oscillatory.md`
- `research/workspace/reports/2026-02-09-claim1-scoped-complete-proof.tex` (de-regularized block framework)

## Goal

Close the remaining regularization gap for the finite-\(g\) multi-mode quartic class:
prove \(\eta\to0^+\) existence with large-\(N\) control.

## Setup

Use the oscillatory regularized family
\[
\omega_{\varepsilon,\eta,N}^{(g)}(F_m)
=
\frac{\int e^{-c_\eta(S_N^{(0)}+gW_N)}F_m(u)\,du\,dv}
{\int e^{-c_\eta(S_N^{(0)}+gW_N)}\,du\,dv},
\quad
c_\eta:=\eta-\frac{i}{\varepsilon},\ \eta>0,
\]
with
\[
S_N^{(0)}(u,v)=P_m(u)+\sum_{j=m+1}^N\frac{d_j(u)}2 v_j^2,\quad
d_j(u)=\lambda_j+2\beta_j(u),\quad d_j(u)\ge\lambda_j\ge\lambda_->0,
\]
\[
W_N(v)=\sum_{m<j<k\le N}b_{jk}v_j^2v_k^2,\quad b_{jk}\ge0,
\]
\[
\rho_N:=\sum_{\max\{j,k\}>N}\frac{b_{jk}}{\lambda_j\lambda_k}\to0.
\]

As in Phase AE, after Gaussian scaling of tail variables:
\[
\omega_{\varepsilon,\eta,N}^{(g)}(F_m)
=
\frac{\int_{\R^m} e^{-c_\eta P_m(u)}F_m(u)\,\Phi_N(u)\,R_{N,\eta}(u)\,du}
{\int_{\R^m} e^{-c_\eta P_m(u)}\Phi_N(u)\,R_{N,\eta}(u)\,du},
\]
\[
\Phi_N(u):=\prod_{j=m+1}^N d_j(u)^{-1/2},
\quad
R_{N,\eta}(u):=\E_{\nu_{N,u}}\!\left[e^{-\kappa_\eta W_N}\right],
\quad
\kappa_\eta:=\frac{g}{c_\eta},
\]
where \(\nu_{N,u}=\bigotimes_{j=m+1}^N\mathcal N(0,d_j(u)^{-1})\).

Define \(\kappa_0:=\lim_{\eta\to0^+}\kappa_\eta=i g\varepsilon\), and
\[
R_{N,0}(u):=\E_{\nu_{N,u}}\!\left[e^{-\kappa_0W_N}\right].
\]

## Theorem 1 (Tail De-Regularization + Uniform \(N\)-Tail Control)

Under the setup above:

1. For each fixed \(N,u\), \(R_{N,\eta}(u)\to R_{N,0}(u)\) as \(\eta\to0^+\).
2. Uniformly in \(\eta\ge0\), \(u\in\R^m\), and \(N'>N\ge m\),
   \[
   |R_{N',\eta}(u)-R_{N,\eta}(u)|
   \le
   g\varepsilon\,\rho_N.
   \]

### Proof

Because \(\Re\kappa_\eta\ge0\) for \(\eta>0\),
\[
|e^{-\kappa_\eta W_N}|\le1.
\]
Also \(\kappa_\eta\to\kappa_0\), so bounded convergence under \(\nu_{N,u}\) gives
\[
R_{N,\eta}(u)\to R_{N,0}(u).
\]

For the tail difference:
\[
|R_{N',\eta}-R_{N,\eta}|
\le
|\kappa_\eta|\E_{\nu_{N',u}}|W_{N'}-W_N|,
\]
using \(|e^{-z_1}-e^{-z_2}|\le |z_1-z_2|\) for \(\Re z_i\ge0\).
Now
\[
|\kappa_\eta|=\frac{g}{|c_\eta|}\le g\varepsilon,
\]
and
\[
\E_{\nu_{N',u}}(W_{N'}-W_N)
=
\sum_{\max\{j,k\}>N}\frac{b_{jk}}{d_j(u)d_k(u)}
\le
\rho_N.
\]
Hence the stated bound. \(\square\)

## Corollary (Claim 1 De-Regularization Closure for This Sector)

Assume the block de-regularized functional framework from the scoped Claim 1 manuscript for observables \(F_m\) in the Gaussian-exponential class, and assume non-vanishing of limiting denominators.

Then:

1. \(\lim_{\eta\to0^+}\omega_{\varepsilon,\eta,N}^{(g)}(F_m)\) exists for each \(N\).
2. The large-\(N\) limit is uniform enough to commute with de-regularization:
   \[
   \lim_{\eta\to0^+}\lim_{N\to\infty}\omega_{\varepsilon,\eta,N}^{(g)}(F_m)
   =
   \lim_{N\to\infty}\lim_{\eta\to0^+}\omega_{\varepsilon,\eta,N}^{(g)}(F_m).
   \]

### Proof sketch

The block part uses the same contour/de-regularization machinery already closed in the manuscript.
The only additional ingredient is the multi-mode factor \(R_{N,\eta}\): Theorem 1 gives both
pointwise \(\eta\to0\) convergence and a uniform \(N\)-tail bound \(O(\rho_N)\).
Combined with the existing \(\Phi_N\) Gaussian-tail control \(O(\sum_{j>N}A_j/\lambda_j)\),
the numerator and denominator are jointly Cauchy in \((\eta,N)\) on the de-regularized contour class,
yielding existence and commuting limits via the standard ratio-difference argument.
\(\square\)

## Status Impact

This closes item 44 in the foundational queue:
the finite-\(g\) non-perturbative multi-mode quartic sector is now controlled at \(\eta=0^+\) in the scoped Claim 1 framework.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_multimode_quartic_dereg_eta0_check.py
```

The script checks numerical stabilization as \(\eta\to0^+\) and simultaneous large-\(N\) refinement for a representative model.

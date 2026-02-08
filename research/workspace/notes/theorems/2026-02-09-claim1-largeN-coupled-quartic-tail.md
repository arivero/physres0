# Claim 1 Phase T: Large-\(N\) Coupled Quartic-Tail Convergence (Beyond Gaussian Tails)

Date: 2026-02-09  
Depends on: `research/workspace/notes/theorems/2026-02-09-claim1-largeN-coupled-gaussian-tail.md`

## Goal

Go beyond the Gaussian-tail large-\(N\) lift by allowing quartic tail terms with mode-coupled observed block dependence.

## Model Class

Fix observed block dimension \(m\ge1\), \(u\in\mathbb R^m\), \(v_j\in\mathbb R\) (\(j>m\)).  
For \(N\ge m\), define
\[
S_N(u,v)
=
P_m(u)+\sum_{j=m+1}^N
\Big(\big(\tfrac{\lambda_j}{2}+\beta_j(u)\big)v_j^2+\gamma_j v_j^4\Big),
\]
with:

1. \(P_m(u)\ge c_4\|u\|^4-c_2\|u\|^2-C_0,\ c_4>0\).
2. \(\lambda_j\ge\lambda_->0,\ \gamma_j\ge\gamma_->0\).
3. \(\beta_j(u)\ge0\), and there exist \(A_j\ge0\) with
   \[
   \beta_j(u)\le A_j\|u\|^2.
   \]

Fix \(\eta>0,\ \varepsilon>0,\ c:=\eta-i/\varepsilon\), and define for bounded cylinder \(F_m\):
\[
\omega_{\varepsilon,\eta,N}(F_m)
:=
\frac{\int e^{-cS_N(u,v)}F_m(u)\,du\,dv}
{\int e^{-cS_N(u,v)}\,du\,dv}.
\]

Define one-mode quartic blocks:
\[
I_j(b):=\int_{\mathbb R}\exp\!\left(-c\big((\tfrac{\lambda_j}{2}+b)t^2+\gamma_j t^4\big)\right)\,dt,
\qquad b\ge0.
\]

Assume:

4. \(I_j(b)\neq0\) for all \(j\) and \(b\ge0\).
5. There exist \(L_j\ge0\) such that
   \[
   \sup_{b\ge0}\left|\partial_b\log I_j(b)\right|\le L_j,
   \qquad
   \sum_{j=m+1}^\infty L_jA_j<\infty.
   \]

## Theorem 1 (Large-\(N\) Convergence)

Under assumptions 1--5, \(\omega_{\varepsilon,\eta,N}(F_m)\) converges as \(N\to\infty\) for each bounded \(F_m\), provided the limiting denominator is nonzero.

### Proof

Integrating out \(v_j\) gives
\[
\omega_{\varepsilon,\eta,N}(F_m)
=
\frac{\int_{\mathbb R^m}e^{-cP_m(u)}F_m(u)\Phi_N(u)\,du}
{\int_{\mathbb R^m}e^{-cP_m(u)}\Phi_N(u)\,du},
\]
where
\[
\Phi_N(u):=\prod_{j=m+1}^N R_j(u),
\qquad
R_j(u):=\frac{I_j(\beta_j(u))}{I_j(0)}.
\]
By mean-value on \(\log I_j\):
\[
|\log R_j(u)|
=
\left|\int_0^{\beta_j(u)}\partial_b\log I_j(b)\,db\right|
\le
L_j\beta_j(u)
\le
L_jA_j\|u\|^2.
\]
Hence
\[
\sum_{j=m+1}^\infty |\log R_j(u)|
\le
\|u\|^2\sum_{j=m+1}^\infty L_jA_j
<\infty,
\]
so \(\Phi_N(u)\to\Phi_\infty(u)\) pointwise.

Also
\[
|\Phi_N(u)|
\le
\exp\!\left(\sum_{j=m+1}^\infty |\log R_j(u)|\right)
\le
\exp(B\|u\|^2),
\quad
B:=\sum_{j=m+1}^\infty L_jA_j.
\]
Therefore
\[
|e^{-cP_m(u)}\Phi_N(u)F_m(u)|
\le
\|F_m\|_\infty\,e^{-\eta P_m(u)}e^{B\|u\|^2},
\]
and the RHS is integrable (quartic coercivity dominates quadratic).
Dominated convergence gives numerator/denominator limits, hence ratio convergence if denominator limit is nonzero. \(\square\)

## Theorem 2 (Tail Cauchy Rate)

With
\[
\tau_N:=\sum_{j=N+1}^\infty L_jA_j,
\]
there exists \(C_{F_m,\varepsilon,\eta}>0\) such that for \(N'>N\ge m\):
\[
|\omega_{\varepsilon,\eta,N'}(F_m)-\omega_{\varepsilon,\eta,N}(F_m)|
\le
C_{F_m,\varepsilon,\eta}\,\tau_N.
\]

### Proof

Let
\[
\Delta_{N,N'}(u):=
\sum_{j=N+1}^{N'}\log R_j(u),
\quad
|\Delta_{N,N'}(u)|\le \|u\|^2\tau_N.
\]
Then
\[
\Phi_{N'}-\Phi_N
=
\Phi_N\big(e^{\Delta_{N,N'}}-1\big),
\]
so using \(|e^z-1|\le |z|e^{|z|}\):
\[
|\Phi_{N'}-\Phi_N|
\le
e^{B\|u\|^2}\,\|u\|^2\tau_N\,e^{\|u\|^2\tau_N}
\le
e^{(B+\tau_m)\|u\|^2}\|u\|^2\tau_N.
\]
Insert in numerator/denominator differences, integrate against \(e^{-\eta P_m}\), and use ratio-difference inequality with denominator bounded away from zero for large \(N\). \(\square\)

## Scope

This closes a non-factorized interacting large-\(N\) class beyond pure Gaussian tails.  
Remaining frontier: deriving assumptions 4--5 intrinsically from uniform renormalized parameter bounds in broader field-theoretic families.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_largeN_coupled_quartic_tail_check.py
```

The script evaluates a sample \(a_j\sim j^{-2}\) quartic-tail family and shows convergence with tail decay.

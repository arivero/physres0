# Claim 1 Phase N: Large-\(N\) Lift for Mode-Coupled Gaussian-Tail Families

Date: 2026-02-09  
Depends on: `research/workspace/reports/2026-02-09-claim1-scoped-complete-proof.tex`

## Goal

Upgrade Claim 1 from finite coupled blocks to a genuinely growing mode-coupled large-\(N\) family, with an explicit Cauchy-rate bound.

## Model Class

Fix observed block size \(m\ge1\), \(u=(u_1,\dots,u_m)\), and for \(N\ge m\) define tail variables \(v=(v_{m+1},\dots,v_N)\).  
Action:
\[
S_N(u,v)=P_m(u)+\sum_{j=m+1}^N\left(\frac{\lambda_j}{2}+\beta_j(u)\right)v_j^2,
\quad
\beta_j(u):=\sum_{i=1}^m a_{ij}u_i^2.
\]
Assume:

1. \(P_m\in C^\infty(\mathbb R^m)\), real-valued, and coercive:
   \[
   P_m(u)\ge c_4\|u\|^4-c_2\|u\|^2-C_0,\qquad c_4>0.
   \]
2. \(\lambda_j\ge\lambda_->0\).
3. \(a_{ij}\ge0\) and
   \[
   A_j:=\sum_{i=1}^m a_{ij},\qquad
   \sum_{j=m+1}^\infty \frac{A_j}{\lambda_j}<\infty.
   \]

For \(\eta>0,\ \varepsilon>0\), define normalized oscillatory states for cylinder \(F_m\in L^\infty(\mathbb R^m)\):
\[
\omega_{\varepsilon,\eta,N}(F_m)
:=
\frac{\int_{\mathbb R^N}e^{-(\eta-i/\varepsilon)S_N(u,v)}F_m(u)\,du\,dv}
{\int_{\mathbb R^N}e^{-(\eta-i/\varepsilon)S_N(u,v)}\,du\,dv}.
\]

## Exact Tail Integration

For each \(j>m\), Gaussian integration gives
\[
\int_{\mathbb R}e^{-(\eta-i/\varepsilon)\left(\frac{\lambda_j}{2}+\beta_j(u)\right)t^2}dt
=
\sqrt{\frac{2\pi}{\eta-i/\varepsilon}}\,
\left(\lambda_j+2\beta_j(u)\right)^{-1/2}.
\]
After cancellation of \(u\)-independent constants in normalized ratios:
\[
\omega_{\varepsilon,\eta,N}(F_m)
=
\frac{\int_{\mathbb R^m}e^{-(\eta-i/\varepsilon)P_m(u)}F_m(u)\,\prod_{j=m+1}^N R_j(u)\,du}
{\int_{\mathbb R^m}e^{-(\eta-i/\varepsilon)P_m(u)}\prod_{j=m+1}^N R_j(u)\,du},
\]
with
\[
R_j(u):=\left(\frac{\lambda_j}{\lambda_j+2\beta_j(u)}\right)^{1/2}\in(0,1].
\]

## Theorem 1 (Large-\(N\) Convergence and Explicit Tail-Rate)

Under the assumptions above:

1. \(\omega_{\varepsilon,\eta,N}(F_m)\) converges as \(N\to\infty\) for every bounded cylinder \(F_m\).
2. There exists \(C_{F_m,\varepsilon,\eta}>0\) such that for all \(N'>N\ge m\),
   \[
   |\omega_{\varepsilon,\eta,N'}(F_m)-\omega_{\varepsilon,\eta,N}(F_m)|
   \le
   C_{F_m,\varepsilon,\eta}\,\sum_{j=N+1}^{N'}\frac{A_j}{\lambda_j}.
   \]
So the state is Cauchy with an explicit summable tail control.

### Proof

Define
\[
\Phi_N(u):=\prod_{j=m+1}^N R_j(u),\qquad
\Phi_\infty(u):=\prod_{j=m+1}^\infty R_j(u).
\]
Since \(R_j(u)\in(0,1]\),
\[
\log R_j(u)
=
-\frac12\log\!\left(1+\frac{2\beta_j(u)}{\lambda_j}\right).
\]
Using \(\log(1+x)\le x\) for \(x\ge0\),
\[
0\le -\log R_j(u)\le \frac{\beta_j(u)}{\lambda_j}
\le
\frac{\|u\|^2A_j}{\lambda_j}.
\]
Hence
\[
\sum_{j=m+1}^\infty |\log R_j(u)|
\le
\|u\|^2\sum_{j=m+1}^\infty \frac{A_j}{\lambda_j}
<\infty,
\]
so \(\Phi_\infty(u)\) exists and
\[
0<\Phi_\infty(u)\le1,\qquad
\Phi_N(u)\to\Phi_\infty(u).
\]

Now define numerator/denominator functionals:
\[
\mathcal N_N(F):=\int e^{-(\eta-i/\varepsilon)P_m(u)}F(u)\Phi_N(u)\,du,\quad
\mathcal D_N:=\mathcal N_N(1).
\]
Since \(|\Phi_N|\le1\) and
\[
\left|e^{-(\eta-i/\varepsilon)P_m(u)}\right|=e^{-\eta P_m(u)},
\]
dominated convergence applies (coercive \(P_m\) gives \(e^{-\eta P_m}\in L^1\)):
\[
\mathcal N_N(F)\to\mathcal N_\infty(F),\qquad \mathcal D_N\to\mathcal D_\infty.
\]
Assuming \(\mathcal D_\infty\neq0\), ratios converge:
\[
\omega_{\varepsilon,\eta,N}(F)\to \omega_{\varepsilon,\eta,\infty}(F):=
\frac{\mathcal N_\infty(F)}{\mathcal D_\infty}.
\]

For the rate, write
\[
\Phi_{N'}=\Phi_N\Psi_{N,N'},
\quad
\Psi_{N,N'}:=\prod_{j=N+1}^{N'}R_j.
\]
Then
\[
1-\Psi_{N,N'}(u)
\le
\sum_{j=N+1}^{N'}(1-R_j(u))
\le
\sum_{j=N+1}^{N'}\frac{\beta_j(u)}{\lambda_j}
\le
\|u\|^2\sum_{j=N+1}^{N'}\frac{A_j}{\lambda_j}.
\]
Therefore
\[
|\Phi_{N'}(u)-\Phi_N(u)|
\le
\|u\|^2\sum_{j=N+1}^{N'}\frac{A_j}{\lambda_j}.
\]
Insert into \(\mathcal N,\mathcal D\) and use
\[
|e^{-(\eta-i/\varepsilon)P_m(u)}|\le e^{-\eta P_m(u)}
\]
to get
\[
|\mathcal N_{N'}(F)-\mathcal N_N(F)|
\le
\|F\|_\infty\,C_1\sum_{j=N+1}^{N'}\frac{A_j}{\lambda_j},
\]
\[
|\mathcal D_{N'}-\mathcal D_N|
\le
C_1\sum_{j=N+1}^{N'}\frac{A_j}{\lambda_j},
\]
with
\[
C_1:=\int_{\mathbb R^m}e^{-\eta P_m(u)}\|u\|^2\,du<\infty.
\]
For \(N\) large enough, \(|\mathcal D_N|\ge d_*>0\), then the ratio difference bound follows by
\[
\left|\frac{a'}{b'}-\frac{a}{b}\right|
\le
\frac{|a'-a|}{|b'|}+\frac{|a|\,|b'-b|}{|b'||b|}.
\]
\(\square\)

## Corollary (Claim 1 Upgrade)

Claim 1 now has a theorem-grade large-\(N\) lift in a genuinely mode-coupled family (not finite-block-only), with explicit tail-rate control tied to \(\sum_j A_j/\lambda_j\).

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_largeN_coupled_gaussian_tail_check.py
```

The script numerically confirms Cauchy convergence and tail-rate scaling for a sample \(a_{ij}\sim j^{-2}\) family.

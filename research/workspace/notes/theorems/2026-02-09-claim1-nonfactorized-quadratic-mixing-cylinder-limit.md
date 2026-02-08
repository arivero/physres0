# Claim 1 Phase AB: Non-Factorized Quadratic-Mixing Cylinder Limit

Date: 2026-02-09  
Depends on: `research/workspace/notes/theorems/2026-02-09-claim1-largeN-coupled-gaussian-tail.md`

## Goal

Close a first non-factorized large-\(N\) field-theory cylinder limit beyond block-tail products by allowing global mode-mixing in the tail quadratic form.

## Model Class

Fix observed block size \(m\ge 1\), \(u\in\mathbb R^m\), and for \(N\ge m\), \(v\in\mathbb R^{N-m}\).  
Define
\[
S_N(u,v)
=
P_m(u)+\frac12\,v^\top\!\big(D_N(u)+K_N\big)v,
\]
where:

1. \(P_m(u)\ge c_4\|u\|^4-c_2\|u\|^2-C_0,\ c_4>0\).
2. \(D_N(u)=\mathrm{diag}(d_{m+1}(u),\dots,d_N(u))\), with
   \[
   d_j(u)=\lambda_j+2\beta_j(u),\quad \lambda_j\ge\lambda_->0,\quad
   \beta_j(u)=\sum_{i=1}^m a_{ij}u_i^2,\ a_{ij}\ge0,
   \]
   and
   \[
   A_j:=\sum_{i=1}^m a_{ij},\qquad
   \sum_{j=m+1}^\infty \frac{A_j}{\lambda_j}<\infty.
   \]
3. \(K=(\kappa_{jk})_{j,k>m}\) is real symmetric and \(K_N\) is its principal truncation.
   Let \(\Lambda=\mathrm{diag}(\lambda_j)_{j>m}\) and
   \[
   \widetilde K:=\Lambda^{-1/2}K\Lambda^{-1/2}.
   \]
   Assume
   \[
   \|\widetilde K\|<\theta<1,\qquad \|\widetilde K\|_1<\infty,
   \]
   and define
   \[
   \tau_N:=\|\widetilde K-P_N\widetilde K P_N\|_1\to0,
   \]
   where \(P_N\) projects onto indices \(m+1,\dots,N\).

For bounded cylinder \(F_m\), set
\[
\omega_{\varepsilon,\eta,N}(F_m)
:=
\frac{\int_{\mathbb R^N}e^{-cS_N(u,v)}F_m(u)\,du\,dv}
{\int_{\mathbb R^N}e^{-cS_N(u,v)}\,du\,dv},
\qquad c=\eta-i/\varepsilon,\ \eta>0.
\]

## Theorem (Large-\(N\) Convergence with Mixed Tail Rate)

Under assumptions 1--3:

1. \(\omega_{\varepsilon,\eta,N}(F_m)\) converges as \(N\to\infty\) for every bounded cylinder \(F_m\), provided the limiting denominator is nonzero.
2. There exists \(C_{F_m,\varepsilon,\eta}>0\) such that for \(N'>N\ge m\),
   \[
   |\omega_{\varepsilon,\eta,N'}(F_m)-\omega_{\varepsilon,\eta,N}(F_m)|
   \le
   C_{F_m,\varepsilon,\eta}
   \left(
   \sum_{j=N+1}^{N'}\frac{A_j}{\lambda_j}
   +\tau_N
   \right).
   \]

So the Cauchy rate splits into:

- diagonal/cylinder tail term \(\sum_{j>N}A_j/\lambda_j\),
- non-factorized mixing tail term \(\tau_N\) (weighted trace-norm truncation of \(K\)).

## Proof

Integrating over \(v\):
\[
\int_{\mathbb R^{N-m}} e^{-c\frac12 v^\top(D_N+K_N)v}dv
=
C_N(c)\,\det(D_N+K_N)^{-1/2},
\]
where \(C_N(c)\) is \(u\)-independent and cancels in normalized ratios.

Hence
\[
\omega_{\varepsilon,\eta,N}(F_m)
=
\frac{\int_{\mathbb R^m} e^{-cP_m(u)}F_m(u)\,\Phi_N(u)\,du}
{\int_{\mathbb R^m} e^{-cP_m(u)}\Phi_N(u)\,du},
\quad
\Phi_N(u):=\det(D_N(u)+K_N)^{-1/2}.
\]

Factor
\[
\Phi_N(u)=\Phi_N^{\mathrm{diag}}(u)\,\Delta_N(u),
\]
with
\[
\Phi_N^{\mathrm{diag}}(u):=\prod_{j=m+1}^N d_j(u)^{-1/2},
\qquad
\Delta_N(u):=\det(I+M_N(u))^{-1/2},
\]
\[
M_N(u):=D_N(u)^{-1/2}K_ND_N(u)^{-1/2}.
\]

### Step 1: Diagonal factor

Exactly as in Phase N, \(\Phi_N^{\mathrm{diag}}\) has a Cauchy tail bound controlled by
\[
\sigma_N:=\sum_{j=N+1}^\infty\frac{A_j}{\lambda_j}.
\]

### Step 2: Non-factorized determinant factor

Because \(D_N(u)\ge \Lambda_N\),
\[
\|M_N(u)\|\le \|\widetilde K\|<\theta,\qquad
\|M_N(u)\|_1\le \|\widetilde K\|_1=:K_1.
\]
Thus \(I+M_N(u)\) is invertible and
\[
|\log\det(I+M_N(u))|
\le
\frac{1}{1-\theta}\|M_N(u)\|_1
\le
\frac{K_1}{1-\theta},
\]
so \(|\Delta_N(u)|\le C_\Delta\) uniformly.

Also, with \(Q(u)=\mathrm{diag}((\lambda_j/d_j(u))^{1/2})\), \(0<Q(u)\le I\), \(Q(u)\) diagonal,
\[
M_\infty(u)=Q(u)\widetilde K Q(u),\qquad
M_N(u)=P_NM_\infty(u)P_N.
\]
Therefore
\[
\|M_\infty(u)-M_N(u)\|_1
\le
\|\widetilde K-P_N\widetilde K P_N\|_1
=\tau_N.
\]
On \(\|A\|,\|B\|\le \theta<1\), the map \(A\mapsto\log\det(I+A)\) is Lipschitz in trace norm:
\[
|\log\det(I+A)-\log\det(I+B)|
\le
\frac{1}{1-\theta}\|A-B\|_1.
\]
Hence
\[
|\Delta_\infty(u)-\Delta_N(u)|\le C'_\Delta\,\tau_N
\]
uniformly in \(u\).

### Step 3: Combine and conclude

From
\[
\Phi_{N'}-\Phi_N
=
\Delta_{N'}(\Phi^{\mathrm{diag}}_{N'}-\Phi^{\mathrm{diag}}_N)
+\Phi^{\mathrm{diag}}_N(\Delta_{N'}-\Delta_N),
\]
we get
\[
|\Phi_{N'}(u)-\Phi_N(u)|
\le
C_1e^{B\|u\|^2}\left(\sigma_N+\tau_N\right)
\]
for constants \(C_1,B\) independent of \(N,u\).  
Multiplying by \(e^{-\eta P_m(u)}\) gives an integrable dominant envelope (quartic coercivity).
Dominated convergence and the standard ratio-difference estimate imply convergence and the stated mixed tail rate.
\(\square\)

## Scope

This is a genuinely non-factorized tail class (global quadratic mode-mixing through \(K\)) and provides a first beyond-block-tail cylinder-limit theorem in the Claim 1 program.

Remaining frontier: extend from quadratic mixing to non-Gaussian multi-mode interactions with comparable explicit rates.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_nonfactorized_quadratic_mixing_check.py
```

The script computes \(\omega_{\varepsilon,\eta,N}(F_m)\) for increasing \(N\) in a decaying-coupling example and compares observed differences with the mixed control term \(\sigma_N+\tau_N\).

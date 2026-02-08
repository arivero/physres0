# Claim 1 Phase H: Gaussian Model Closure of H1-H6

Date: 2026-02-08  
Depends on: `research/workspace/notes/theorems/2026-02-08-claim1-continuum-skeleton.md`

## Setup

Let \(X_N=\mathbb R^N\), \(\pi_{N\to m}(x_1,\dots,x_N)=(x_1,\dots,x_m)\), and let \((\lambda_j)_{j\ge 1}\) satisfy
\[
0<\lambda_-\le \lambda_j\le \lambda_+<\infty.
\]
Define renormalized Gaussian actions
\[
S_N^{\mathrm{ren}}(x)=\frac12\sum_{j=1}^N \lambda_j x_j^2.
\]
For \(F_m\in C_b^2(\mathbb R^m)\) and \(N\ge m\), define
\[
\omega_{\varepsilon,N}(F_m)
:=
\frac{\int_{\mathbb R^N}e^{\frac{i}{\varepsilon}S_N^{\mathrm{ren}}(x)}\,
F_m(x_1,\dots,x_m)\,dx}
{\int_{\mathbb R^N}e^{\frac{i}{\varepsilon}S_N^{\mathrm{ren}}(x)}\,dx},
\qquad \varepsilon>0.
\]

## Theorem 1 (Exact Projective Stability)

For every \(m\), every \(F_m\in C_b^2(\mathbb R^m)\), every \(\varepsilon>0\), and every \(N\ge m\),
\[
\omega_{\varepsilon,N}(F_m)=\omega_{\varepsilon,m}(F_m).
\]
Hence the \(N\to\infty\) limit exists exactly (no remainder), and the Cauchy defect is identically zero.

Proof:

1. Factor numerator/denominator into first \(m\) coordinates and tail \(j>m\).
2. Tail oscillatory Gaussian factors cancel in the ratio.
3. Remaining expression is precisely \(\omega_{\varepsilon,m}(F_m)\).

## Corollary 1 (H1-H6 Are Verified in This Model)

Relative to the continuum skeleton hypotheses:

1. H1: projective compatibility is exact by coordinate splitting.
2. H2: nondegeneracy holds uniformly from \(\lambda_-\le\lambda_j\le\lambda_+\).
3. H3: normalization nonvanishing holds because each 1D oscillatory Gaussian factor is nonzero.
4. H4: counterterm flow can be chosen identically zero (already renormalized form).
5. H5: continuity in \(F_m\) follows from
   \[
   |\omega_{\varepsilon,N}(F_m)|\le \|F_m\|_\infty.
   \]
6. H6: Cauchy tail bound is exact with \(\alpha_m(N,N')\equiv 0\).

Therefore the continuum state \(\omega_\varepsilon\) on cylinder observables exists and is unique for this Gaussian family.

## Theorem 2 (Counterterm Repair from an Incompatible Bare Family)

Suppose bare coefficients are
\[
\lambda_{j,N}^{\mathrm{bare}}=\lambda_j+r_{j,N},
\]
with \(|r_{j,N}|\le \lambda_-/2\), and for each fixed \(j\), \(r_{j,N}\) may depend on \(N\) (breaking projective compatibility).

Define local counterterms
\[
\delta\lambda_{j,N}:=-r_{j,N},\qquad
\lambda_{j,N}^{\mathrm{ren}}:=\lambda_{j,N}^{\mathrm{bare}}+\delta\lambda_{j,N}=\lambda_j.
\]
Then renormalized actions recover Theorem 1 exactly; in particular, H1-H6 hold after renormalization.

Interpretation: this provides an explicit constructive instance of the skeleton renormalization map \(\mathcal R_N\).

## Proposition 3 (Semiclassical Channel Expansion in the Gaussian Core)

For \(F_m\in C_b^\infty(\mathbb R^m)\), define
\[
\mathcal L_m:=\sum_{j=1}^m \lambda_j^{-1}\partial_{x_j}^2.
\]
Then
\[
\omega_\varepsilon(F_m)
=
\left[e^{\frac{i\varepsilon}{2}\mathcal L_m}F_m\right]_{x=0}
=
\sum_{k=0}^{K-1}\frac{1}{k!}\left(\frac{i\varepsilon}{2}\right)^k
(\mathcal L_m^kF_m)(0)
+R_{K,\varepsilon}(F_m).
\]

Consequences:

1. \(\omega_\varepsilon(F_m)\to F_m(0)\) as \(\varepsilon\to 0\).
2. Higher terms correspond to derivative-at-zero channels (even-order \(\delta^{(m)}\)-type modes in 1D language).

So in this closed model, the channel hierarchy is explicit and controlled.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_gaussian_h1_h6_closure_check.py
```

The script verifies:

1. exact \(N\)-independence in the compatible Gaussian family,
2. oscillation in an incompatible bare family,
3. restored \(N\)-independence after counterterm repair,
4. \(\varepsilon\to 0\) trend to \(F(0)\) for a smooth Gaussian test observable.

# Claim 1 Phase K: \(\eta\to0^+\) Closure for Factorized Quartic Blocks

Date: 2026-02-08  
Depends on: `research/workspace/notes/theorems/2026-02-08-claim1-small-coupling-perturbation-closure.md`

## Scope

Close the regularization gap for the factorized quartic interacting class (same product structure as Phase I), for Gaussian-exponential cylinder observables.

## 1D Block Definition

Fix \(\lambda>0\), \(\kappa>0\), \(g>0\), \(\varepsilon>0\), \(\alpha\ge 0\).  
Define
\[
I_\eta(\alpha)
:=
\int_{\mathbb R}
\exp\!\left[-(\eta-i/\varepsilon)\left(\frac{\lambda}{2}x^2+g\kappa x^4\right)-\alpha x^2\right]dx,
\qquad \eta\ge 0.
\]

For \(\eta>0\), this is absolutely convergent on \(\mathbb R\).

## Contour Representation at \(\eta=0\)

Use \(x=e^{i\pi/8}y\), \(dx=e^{i\pi/8}dy\). Then
\[
I_0(\alpha)
=
e^{i\pi/8}
\int_{\mathbb R}
\exp\!\left[
\frac{i}{\varepsilon}\left(
\frac{\lambda}{2}e^{i\pi/4}y^2+g\kappa e^{i\pi/2}y^4
\right)-\alpha e^{i\pi/4}y^2
\right]dy.
\]
Since \(e^{i\pi/2}=i\), the quartic term contributes real decay
\[
\Re\left(\frac{i}{\varepsilon}g\kappa e^{i\pi/2}y^4\right)
=-\frac{g\kappa}{\varepsilon}y^4,
\]
so the contour integral is absolutely convergent.

## Theorem (Block \(\eta\to0^+\) Limit)

For the contour-defined branch above,
\[
\lim_{\eta\to0^+} I_\eta(\alpha)=I_0(\alpha).
\]

Proof sketch:

1. For \(\eta\in[0,\eta_0]\), write all integrals on the same rotated contour.
2. Integrands are analytic in \((\eta,y)\) and converge pointwise as \(\eta\to0^+\).
3. Uniform bound:
   \[
   |f_\eta(y)|\le C\exp\!\left(-c_4y^4+c_2y^2\right),
   \]
   with \(c_4=g\kappa/\varepsilon>0\), independent of \(\eta\).
4. Apply dominated convergence.

## Cylinder Expectation Closure (Factorized Product Class)

For \(X_N=\mathbb R^N\) with product action
\[
S_N^{(g)}(x)=\sum_{j=1}^N\left(\frac{\lambda_j}{2}x_j^2+g\kappa_jx_j^4\right),
\]
and cylinder observable
\[
F_m(x)=\exp\!\left(-\sum_{j=1}^m\alpha_jx_j^2\right),
\]
normalized state is
\[
\omega_{\varepsilon,\eta,N}^{(g)}(F_m)
=
\prod_{j=1}^m \frac{I_{\eta,j}(\alpha_j)}{I_{\eta,j}(0)},
\]
with exact \(N\)-stability by tail cancellation.

Applying the 1D block theorem coordinate-wise:
\[
\lim_{\eta\to0^+}\omega_{\varepsilon,\eta,N}^{(g)}(F_m)
=
\prod_{j=1}^m\frac{I_{0,j}(\alpha_j)}{I_{0,j}(0)}
:
\omega_{\varepsilon,0}^{(g)}(F_m).
\]

So the regularization gap is removed for this interacting factorized quartic class and this cylinder-observable class.

## Boundary of This Result

Still open:

1. non-factorized interactions (mode coupling),
2. broader observable classes beyond Gaussian-exponential cylinders,
3. uniform channel-expansion control in \(\varepsilon\to0\) for interacting sectors.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_eta_zero_quartic_block_check.py
```

The script compares \(\eta>0\) real-axis values to the \(\eta=0\) rotated-contour target for a representative quartic block and confirms convergence of normalized expectations.

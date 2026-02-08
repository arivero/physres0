# Claim 1 Phase J: Removing the \(\eta>0\) Regulator in the Gaussian Sector

Date: 2026-02-08  
Depends on: `research/workspace/notes/theorems/2026-02-08-claim1-gaussian-h1-h6-closure.md`  
Context: `research/workspace/notes/theorems/2026-02-08-claim1-small-coupling-perturbation-closure.md`

## Scope

This note closes the \(\eta\to0^+\) regularization gap exactly for the Gaussian core.  
It does not yet close the same gap for interacting quartic terms.

## Gaussian Regularized Family

Fix \(\varepsilon>0\), \(X_N=\mathbb R^N\), and
\[
S_N(x)=\frac12\sum_{j=1}^N\lambda_jx_j^2,\qquad
0<\lambda_-\le\lambda_j\le\lambda_+.
\]
For \(\eta>0\), define normalized states
\[
\omega_{\varepsilon,\eta,N}(F_m)
:=
\frac{\int_{\mathbb R^N}\exp\!\left[-(\eta-i/\varepsilon)S_N(x)\right]F_m(x_1,\dots,x_m)\,dx}
{\int_{\mathbb R^N}\exp\!\left[-(\eta-i/\varepsilon)S_N(x)\right]\,dx},
\qquad N\ge m.
\]

As in Phase H, these are exactly \(N\)-stable for cylinder observables.

## Theorem (Exact \(\eta\to0^+\) Limit for Gaussian-Exponential Cylinder Class)

Take
\[
F_m(x_1,\dots,x_m)=\exp\!\left(-\sum_{j=1}^m\alpha_jx_j^2\right),
\qquad \alpha_j\ge 0.
\]
Then for each \(N\ge m\),
\[
\omega_{\varepsilon,\eta,N}(F_m)
=
\prod_{j=1}^m
\left(
\frac{\lambda_j(\eta-i/\varepsilon)}
{\lambda_j(\eta-i/\varepsilon)+\alpha_j}
\right)^{1/2}.
\]
Hence
\[
\lim_{\eta\to0^+}\omega_{\varepsilon,\eta,N}(F_m)
=
\prod_{j=1}^m
\left(
\frac{-i\lambda_j/\varepsilon}
{\alpha_j-i\lambda_j/\varepsilon}
\right)^{1/2}
:
\omega_{\varepsilon,0}(F_m),
\]
with branch fixed continuously from \(\eta>0\).

Proof:

1. Factorize numerator and denominator into 1D Gaussian integrals.
2. Evaluate each factor explicitly via \(\int e^{-a x^2}dx=\sqrt{\pi/a}\) for \(\Re a>0\).
3. Cancel tail factors (\(j>m\)).
4. Take \(\eta\to0^+\) in the explicit finite product.

## Corollary (Gaussian De-Regularization Closed)

For this cylinder class:

1. the regularized states converge to a well-defined oscillatory/Fresnel normalized state,
2. projective \(N\)-stability survives the limit,
3. Claim 1 continuum skeleton now has a regulator-free Gaussian sector.

## What Remains Open

For interacting quartic/polynomial perturbations (Phase I model), one still needs uniform contour/deformation estimates to pass \(\eta\to0^+\) while keeping the same cylinder-limit control.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_eta_zero_gaussian_limit_check.py
```

The script evaluates the explicit formula above for decreasing \(\eta\), confirming convergence to the \(\eta=0\) Fresnel expression.

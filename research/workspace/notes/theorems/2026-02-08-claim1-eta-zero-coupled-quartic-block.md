# Claim 1 Phase L: \(\eta\to0^+\) Closure for a Coupled Quartic Block

Date: 2026-02-08  
Builds on: `research/workspace/notes/theorems/2026-02-08-claim1-eta-zero-quartic-product-closure.md`

## Scope

Move beyond factorized interactions by treating a finite-dimensional mode-coupled quartic block.

## Coupled 2D Block

Fix \(\lambda_1,\lambda_2>0\), \(\kappa_1,\kappa_2>0\), \(\mu\ge 0\), \(g>0\), \(\varepsilon>0\).  
Define
\[
Q_2(x)=\frac12(\lambda_1x_1^2+\lambda_2x_2^2),\qquad
Q_4(x)=\kappa_1x_1^4+\kappa_2x_2^4+\mu x_1^2x_2^2.
\]
For \(\eta\ge 0\) and \(\alpha_1,\alpha_2\ge 0\),
\[
I_\eta(\alpha_1,\alpha_2)
:=
\iint_{\mathbb R^2}
\exp\!\left[-(\eta-i/\varepsilon)\left(Q_2(x)+gQ_4(x)\right)-\alpha_1x_1^2-\alpha_2x_2^2\right]dx.
\]

## Rotated Contour at \(\eta=0\)

Set \(x_j=e^{i\pi/8}y_j\). Then
\[
Q_4(x)=e^{i\pi/2}Q_4(y)=iQ_4(y),
\]
so
\[
\Re\!\left(\frac{i}{\varepsilon}gQ_4(x)\right)
=-\frac{g}{\varepsilon}Q_4(y)\le -\frac{gc}{\varepsilon}\|y\|^4,
\]
for some \(c>0\) (coercivity from \(\kappa_1,\kappa_2>0,\mu\ge0\)).

Hence the \(\eta=0\) rotated integral is absolutely convergent.

## Theorem (Finite-Dimensional Coupled Block \(\eta\to0^+\) Limit)

Define the normalized block expectation
\[
E_\eta(\alpha_1,\alpha_2)
:=
\frac{I_\eta(\alpha_1,\alpha_2)}{I_\eta(0,0)}.
\]
Then, with the branch determined by the rotated contour at angle \(\pi/8\),
\[
\lim_{\eta\to0^+}E_\eta(\alpha_1,\alpha_2)=E_0(\alpha_1,\alpha_2).
\]

Proof sketch:

1. Represent all integrals on the same rotated contour.
2. Integrands converge pointwise as \(\eta\to0^+\).
3. Uniform bound:
   \[
   |f_\eta(y)|\le C\exp\!\left(-c_4\|y\|^4+c_2\|y\|^2\right),
   \]
   with \(c_4>0\) independent of \(\eta\in[0,\eta_0]\).
4. Apply dominated convergence to numerator and denominator, then divide.

## Consequence for Claim 1 Program

The \(\eta\to0^+\) de-regularization is now closed for a non-factorized interacting finite block (mode-coupled quartic polynomial), not only product quartic terms.

## Remaining Gap

Still open:

1. projective/infinite-dimensional mode-coupled families with uniform \(N\)-control,
2. compatibility of this de-regularization with full cylinder-limit hypotheses H1-H6 at large \(N\).

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_eta_zero_coupled_quartic_block_check.py
```

The script numerically confirms \(E_\eta\to E_0\) for a representative coupled quartic block.

# Claim 1 Phase BT (AN-27): \(d=3\) Oscillatory/De-Regularized Transfer of the Widened Local Class

Date: 2026-02-09 (CET)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-class-extension-local-cb-channel.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-cb1-tail-insertion-closure.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-insertion-lq-moment-verification.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-fd-schwinger-dyson-identity.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-partition-nonvanishing-bounds.md`

## Goal

Execute AN-27: transfer the AN-25 widened local classes
\(C_c\to C_b\) and \(C_c^1\to C_b^1\) from the scoped Euclidean branch to the
oscillatory regularized branch \(c_\eta=\eta-i/h\), and pass to
de-regularization \(\eta\to0^+\) in the same \(d=3\) lane.

## Target/Model/Existence Declaration (Non-Drift Rule)

1. target dimension: \(d=3\),
2. model class: AN-24 nearest-neighbor lattice \(\phi^4\), finite volume,
3. existence notion: local-class transfer of already-closed AN-25/AN-26/AN-26B
   identities to oscillatory/de-regularized normalized states,
4. geometric \(1/2\)-density role: interpretation only.

## Setup

Use the AN-24 finite-volume action \(S_{a,L}^{(\kappa)}\), \(0<a\le1\),
\(\kappa\in[0,\kappa_*]\), and define
\[
c_\eta:=\eta-\frac{i}{h},\qquad \eta\in[0,\eta_*],\ h>0.
\]

Fix rotation angle \(\theta:=\pi/8\) and contour map
\[
\phi_x=e^{-i\theta}y_x,\qquad y\in\mathbb R^{|\Lambda_{a,L}|}.
\]
For local observable \(F\), define oscillatory contour functional
\[
\mathcal I_{\eta,a,L}^{(\kappa)}(F)
:=
e^{-i\theta|\Lambda_{a,L}|}\!\int_{\mathbb R^{|\Lambda_{a,L}|}}
\exp\!\left(-c_\eta S_{a,L}^{(\kappa)}(e^{-i\theta}y)\right)
F(e^{-i\theta}y)\,dy.
\]
Normalized state:
\[
\omega_{\eta,a,L}^{(\kappa)}(F)
:=
\frac{\mathcal I_{\eta,a,L}^{(\kappa)}(F)}
{\mathcal I_{\eta,a,L}^{(\kappa)}(1)}.
\]

For a fixed local block \(B\), renormalized coordinates are
\[
v_B=a^{3/2}(\phi_x)_{x\in B}.
\]
Keep AN-25 class names:
\[
\mathcal A_{B,\mathrm{ext}}^{\mathrm{ren}}
=
\{f(v_B):f\in C_b(\mathbb R^{|B|})\},
\quad
\mathcal T_{B,\mathrm{ext}}^{\mathrm{ren}}
=
\{\tilde\psi(v_B):\tilde\psi\in C_b^1(\mathbb R^{|B|})\}.
\]

## Assumption Package for AN-27

1. **(NZ)** uniform non-vanishing denominator in branch window:
   \[
   \inf_{\eta\in[0,\eta_*],a,L,\kappa}
   \left|\mathcal I_{\eta,a,L}^{(\kappa)}(1)\right|
   \ge z_*>0.
   \]
2. **(ENV)** contour-envelope bound: there exist \(C_*,\alpha_*,\beta_*>0\)
   independent of \((\eta,a,L,\kappa)\) such that
   \[
   \left|\exp\!\left(-c_\eta S_{a,L}^{(\kappa)}(e^{-i\theta}y)\right)\right|
   \le
   C_*\exp\!\left(
   -\alpha_*a^3\!\sum_x y_x^4+\beta_*a^3\!\sum_x y_x^2
   \right).
   \]
3. **(AN26B-INS)** insertion growth is polynomial in local fields
   (true for \(\partial_{\phi_i}S\)), so envelope moments control
   \(\nu_*(|\partial_iS|^{4/3})<\infty\), where \(\nu_*\) is the normalized
   positive envelope measure from (ENV).

Remarks:

1. (NZ) is the oscillatory counterpart of the partition non-vanishing control
   from Phase O.
2. (ENV) uses \(\theta=\pi/8\): quartic term gains strict damping in modulus,
   while lower-order terms are absorbed into \(+\beta_*|y|^2\).

## Theorem 1 (Oscillatory Regularized Class Transfer, \(\eta\in(0,\eta_*]\))

Under (NZ)+(ENV)+(AN26B-INS), AN-25 class extension is valid for every
\(\eta>0\) in the branch window:

1. \(C_c\to C_b\) local observable extension in
   \(\mathcal A_{B,\mathrm{ext}}^{\mathrm{ren}}\),
2. \(C_c^1\to C_b^1\) SD test extension in
   \(\mathcal T_{B,\mathrm{ext}}^{\mathrm{ren}}\),
3. SD identity
   \[
   \omega_{\eta,a,L}^{(\kappa)}(\partial_i\psi)
   =
   c_\eta\,\omega_{\eta,a,L}^{(\kappa)}\!\left(\psi\,\partial_iS\right)
   \]
   holds for bounded local \(C_b^1\) tests.

### Proof sketch

For any local \(G\), triangle inequality with (NZ) gives
\[
\left|\omega_{\eta,a,L}^{(\kappa)}(G)\right|
\le
\frac{1}{z_*}\int \left|e^{-c_\eta S(e^{-i\theta}y)}\right|\,|G(e^{-i\theta}y)|\,dy.
\]
Apply (ENV) to dominate by \(L^1(\nu_*)\)-moments.

1. **Observable side:** cutoff \(f_R=\chi_R f\) as in AN-25.
   Tail error is bounded by \(\|f\|_\infty\nu_*(\|v_B\|>R)\), which is
   \(O(R^{-2})\) by envelope second moments.
2. **Test side:** same AN-26 decomposition with \(\psi_R=\chi_R\psi\):
   derivative cutoff term vanishes by moment tails, and insertion-tail term is
   controlled by Holder with \(q=4/3\) using (AN26B-INS).
3. SD for \(\psi_R\in C_c^1\) is finite-volume standard
   (Phase Q, regularized branch), then pass \(R\to\infty\).
\(\square\)

## Theorem 2 (De-Regularized Transfer at \(\eta=0\))

Under the same package, the limits
\[
\omega_{0,a,L}^{(\kappa)}(F)
:=
\lim_{\eta\to0^+}\omega_{\eta,a,L}^{(\kappa)}(F)
\]
exist for local \(F\in\mathcal A_{B,\mathrm{ext}}^{\mathrm{ren}}\) and
\(\psi\in\mathcal T_{B,\mathrm{ext}}^{\mathrm{ren}}\), and satisfy
\[
\omega_{0,a,L}^{(\kappa)}(\partial_i\psi)
=
\left(-\frac{i}{h}\right)\,
\omega_{0,a,L}^{(\kappa)}\!\left(\psi\,\partial_iS\right).
\]

### Proof sketch

1. pointwise \(\eta\to0^+\) convergence of integrands is immediate,
2. (ENV) provides \(\eta\)-uniform integrable domination for numerator and
   denominator terms on the local classes,
3. (NZ) prevents denominator collapse, so ratio limits are valid,
4. pass \(\eta\to0^+\) in Theorem 1 SD identity.
\(\square\)

## Corollary (AN-27 Closure in Scoped \(d=3\) Lane)

AN-27 is closed, in theorem form, for the finite-volume local-renormalized
branch under explicit non-vanishing and contour-envelope assumptions:

1. AN-25 widened classes transfer to oscillatory regularized branch,
2. same classes persist through de-regularization \(\eta\to0^+\),
3. SD identity persists for bounded local \(C_b^1\) tests at \(\eta=0\).

AN-28 now closes first nonlocal-cylinder extension in:
`research/workspace/notes/theorems/2026-02-09-claim1-d3-an28-nonlocal-cylinder-transfer.md`.
Next target (AN-29): continuum extraction for those nonlocal cylinders with
explicit refinement-Cauchy control in the same branch.

## Validation Contract

### Assumptions

1. AN-24 finite-volume \(d=3\) branch and AN-25/AN-26/AN-26B local setup,
2. denominator non-vanishing (NZ) on \(\eta\in[0,\eta_*]\),
3. contour envelope (ENV) and insertion-moment control (AN26B-INS).

### Units and dimensions check

1. renormalized local coordinates \(v_B=a^{3/2}\phi_B\) are unchanged,
2. insertion channel remains \(\partial_iS\), same as AN-26/AN-26B.

### Symmetry/conservation checks

1. same finite-volume periodic lattice symmetries as AN-24,
2. no new model term is introduced; only contour representation changes.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an27_oscillatory_dereg_transfer_check.py
```

The script checks, in a low-dimensional contour-rotation surrogate:

1. denominator non-vanishing over \(\eta\in[0,\eta_*]\),
2. \(C_b\)-observable de-regularization stabilization,
3. insertion-tail bounds versus cutoff radius \(R\),
4. SD residual behavior for bounded \(C_b^1\) tests and cutoff-approximant drift.

### Confidence statement

AN-27 is theorem-grade in the scoped finite-volume branch under explicit
(NZ)+(ENV) assumptions. Global continuum interacting closure remains open.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic parameter grid printed by script,
3. date anchor: 2026-02-09 (US).

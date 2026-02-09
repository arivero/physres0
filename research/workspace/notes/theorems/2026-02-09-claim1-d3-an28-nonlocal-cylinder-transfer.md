# Claim 1 Phase BU (AN-28): \(d=3\) First Nonlocal-Cylinder Transfer in Oscillatory/De-Regularized Branch

Date: 2026-02-09 (CET)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-oscillatory-dereg-class-transfer.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-insertion-lq-moment-verification.md`

## Goal

Strengthen Claim 1 after AN-27 by extending from strictly single-block local
classes to a first disconnected two-block nonlocal-cylinder family in the same
\(d=3\) oscillatory/de-regularized branch.

## Target/Model/Existence Declaration (Non-Drift Rule)

1. target dimension: \(d=3\),
2. model class: AN-24 nearest-neighbor lattice \(\phi^4\), finite volume,
3. existence notion: class transfer for disconnected finite-cylinder observables
   and SD-test channels in oscillatory/de-regularized normalized states,
4. geometric \(1/2\)-density role: interpretation only.

## Setup

Use AN-27 oscillatory contour branch:
\[
c_\eta=\eta-\frac{i}{h},\qquad \eta\in[0,\eta_*],\ h>0,
\]
with normalized states \(\omega_{\eta,a,L}^{(\kappa)}\).

Take two disjoint local blocks \(B_1,B_2\subset\Lambda_{a,L}\),
\(B_1\cap B_2=\varnothing\), and renormalized coordinates
\[
v_{B_j}=a^{3/2}(\phi_x)_{x\in B_j},\qquad j=1,2.
\]

Define disconnected nonlocal-cylinder classes:
\[
\mathcal A_{B_1,B_2}^{\mathrm{nl}}
:=
\left\{
F(\phi)=f(v_{B_1},v_{B_2}): f\in C_b(\mathbb R^{|B_1|+|B_2|})
\right\},
\]
\[
\mathcal T_{B_1,B_2}^{\mathrm{nl}}
:=
\left\{
\psi(\phi)=\tilde\psi(v_{B_1},v_{B_2}): \tilde\psi\in C_b^1(\mathbb R^{|B_1|+|B_2|})
\right\}.
\]

## Assumption Package (AN-28)

1. **(NZ2)** non-vanishing denominator in branch window:
   \[
   \inf_{\eta\in[0,\eta_*],a,L,\kappa}
   \left|\mathcal I_{\eta,a,L}^{(\kappa)}(1)\right|\ge z_*>0.
   \]
2. **(ENV2)** same AN-27 contour envelope bound for absolute integrability.
3. **(MOM2)** envelope-induced second moments on \(v_{B_1},v_{B_2}\):
   \[
   \sup_{\eta,a,L,\kappa}\omega_\eta\!\left(\|v_{B_1}\|^2+\|v_{B_2}\|^2\right)
   \le C_{12}<\infty.
   \]
4. **(INS2)** insertion \(L^{4/3}\)-moment gate (AN-26B style) in this branch:
   \[
   \sup_{\eta,a,L,\kappa}\omega_\eta\!\left(|\partial_iS|^{4/3}\right)\le M_{i,4/3}<\infty
   \quad(i\in B_1).
   \]

## Theorem 1 (Oscillatory Transfer for Two-Block Nonlocal Cylinders)

Under (NZ2)+(ENV2)+(MOM2)+(INS2), for every \(\eta\in(0,\eta_*]\):

1. compact-support disconnected cylinders extend uniquely to
   \(\mathcal A_{B_1,B_2}^{\mathrm{nl}}\),
2. SD test-side extension holds on \(\mathcal T_{B_1,B_2}^{\mathrm{nl}}\):
   \[
   \omega_\eta(\partial_i\psi)
   =
   c_\eta\,\omega_\eta\!\left(\psi\,\partial_iS\right),\qquad i\in B_1.
   \]

### Proof sketch

Let \(w=(v_{B_1},v_{B_2})\). Use cutoff \(\chi_R(w)\) and approximants
\(f_R=\chi_R f,\ \psi_R=\chi_R\psi\).

1. observable tails:
   \[
   |\omega_\eta(f-f_R)|
   \le \|f\|_\infty\,\omega_\eta(\|w\|>R)
   \le \|f\|_\infty\,\frac{C_{12}}{R^2},
   \]
   by Markov from (MOM2).
2. test-side insertion tails:
   \[
   \omega_\eta\!\left(|\partial_iS|\mathbf 1_{\|w\|>R}\right)
   \le
   M_{i,4/3}^{3/4}\,
   \omega_\eta(\|w\|>R)^{1/4}
   \xrightarrow[R\to\infty]{}0,
   \]
   by Holder with \(q=4/3\), \(q'=4\).
3. SD holds for compactly supported approximants (AN-27 finite-volume branch);
   pass \(R\to\infty\).
\(\square\)

## Theorem 2 (De-Regularized Persistence at \(\eta=0\))

Under the same package, the limit
\[
\omega_0(F)=\lim_{\eta\to0^+}\omega_\eta(F)
\]
exists on \(\mathcal A_{B_1,B_2}^{\mathrm{nl}}\cup\mathcal T_{B_1,B_2}^{\mathrm{nl}}\),
and
\[
\omega_0(\partial_i\psi)
=
\left(-\frac{i}{h}\right)\omega_0\!\left(\psi\,\partial_iS\right),\qquad i\in B_1.
\]

### Proof sketch

1. pointwise integrand convergence in \(\eta\to0^+\),
2. branch-uniform domination from (ENV2),
3. denominator stability from (NZ2),
4. ratio-limit passage in Theorem 1 identities.
\(\square\)

## Corollary (AN-28 Scoped Strengthening)

AN-28 closes a first nonlocal-cylinder strengthening of Claim 1 in the
scoped \(d=3\) oscillatory/de-regularized lane:

1. disconnected two-block bounded cylinders are included,
2. SD-test extension remains valid on bounded \(C_b^1\) two-block tests,
3. de-regularized branch keeps the same nonlocal-cylinder identities.

Next target (AN-29): continuum extraction for these disconnected nonlocal
cylinders with explicit refinement-Cauchy control.

## Validation Contract

### Assumptions

1. AN-27 branch assumptions plus two-block moment/insertion controls (MOM2, INS2),
2. finite-volume \(d=3\) setting and fixed \(h>0\).

### Units and dimensions check

1. renormalized coordinates \(v_{B_j}=a^{3/2}\phi_{B_j}\) unchanged,
2. insertion channel remains \(\partial_iS\), same physical dimension lane.

### Symmetry/conservation checks

1. same periodic lattice symmetries as AN-24/AN-27,
2. disconnected-block extension introduces no new interaction term.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an28_nonlocal_cylinder_transfer_check.py
```

The script checks in a two-variable disconnected-cylinder surrogate:

1. denominator non-vanishing over \(\eta\in[0,\eta_*]\),
2. de-regularization stabilization for a bounded two-block observable,
3. insertion-tail decay in combined two-block norm,
4. cutoff-approximant drift decay and SD residual behavior.

### Confidence statement

AN-28 is theorem-grade in this scoped finite-volume branch under explicit
assumptions. Global continuum interacting closure remains open.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic parameter/grid settings printed by script,
3. date anchor: 2026-02-09 (US).

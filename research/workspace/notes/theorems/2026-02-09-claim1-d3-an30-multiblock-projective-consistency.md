# Claim 1 Phase BW (AN-30): \(d=3\) Multi-Block Nonlocal Cylinders and Projective Consistency

Date: 2026-02-09 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-an29-nonlocal-continuum-cauchy.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-an28-nonlocal-cylinder-transfer.md`

## Goal

Close the next Claim 1 step after AN-29: extend disconnected two-block control
to finite graph-indexed multi-block nonlocal cylinders with explicit
combinatorial constants and projective-consistency bookkeeping.

## Target/Model/Existence Declaration (Non-Drift Rule)

1. target dimension: \(d=3\),
2. model class: AN-24/AN-29 nearest-neighbor lattice \(\phi^4\), finite volume,
3. existence notion: refinement-limit existence and projective consistency for
   finite graph-indexed nonlocal observable/test families,
4. geometric \(1/2\)-density role: interpretation only.

## Setup

Let \(H=(V_H,E_H)\) be a finite graph indexing disjoint local blocks
\(\{B_v\}_{v\in V_H}\), and define renormalized block coordinates
\[
v_{B_v}=a^{3/2}\phi|_{B_v}.
\]

Define graph-indexed nonlocal classes:
\[
\mathcal A_H^{\mathrm{nl}}=
\left\{
F(\phi)=f\!\left((v_{B_v})_{v\in V_H}\right):\ f\in C_b(\mathbb R^{M_H})
\right\},
\quad
M_H:=\sum_{v\in V_H}|B_v|,
\]
\[
\mathcal T_H^{\mathrm{nl}}=
\left\{
\psi(\phi)=\tilde\psi\!\left((v_{B_v})_{v\in V_H}\right):\
\tilde\psi\in C_b^1(\mathbb R^{M_H})
\right\}.
\]

For scale index \(\ell\), let
\[
\rho_\ell:=a_\ell^\alpha+L_\ell^{-\beta},\qquad \alpha,\beta>0,
\]
and normalized oscillatory/de-regularized states
\[
\omega_{\eta,\ell,H}^{(\kappa)}(F)=
\frac{\mathcal I_{\eta,\ell,H}^{(\kappa)}(F)}
{\mathcal I_{\eta,\ell,H}^{(\kappa)}(1)},
\qquad
c_\eta=\eta-\frac{i}{h}.
\]

## Assumption Package (AN-30)

For each finite graph \(H\) in a fixed family \(\mathfrak H\):

1. **(NZ4)** graph-uniform denominator lower bound:
   \[
   \inf_{\eta,\ell,\kappa,H\in\mathfrak H}
   \left|\mathcal I_{\eta,\ell,H}^{(\kappa)}(1)\right|\ge z_*>0.
   \]
2. **(RCN-H)** graph-indexed numerator/denominator Cauchy rates:
   \[
   |\Delta N_H(\ell,m)|\le C_{F,H}(\rho_\ell+\rho_m),\qquad
   |\Delta Z_H(\ell,m)|\le C_{1,H}(\rho_\ell+\rho_m).
   \]
3. **(BND-H)** graph-indexed numerator bound:
   \[
   \sup_{\eta,\ell,\kappa}
   |\mathcal I_{\eta,\ell,H}^{(\kappa)}(F)|\le M_{F,H}.
   \]
4. **(COMB-H)** combinatorial growth control:
   \[
   C_{F,H}\le C_F^\star(1+|E_H|),\quad
   C_{1,H}\le C_1^\star(1+|E_H|),\quad
   M_{F,H}\le M_F^\star(1+|V_H|).
   \]
5. **(PROJ-H)** finite-scale restriction defect for induced subgraphs
   \(H'\subseteq H\):
   \[
   \left|
   \omega_{\eta,\ell,H}^{(\kappa)}(F'\circ\pi_{H\to H'})
   -
   \omega_{\eta,\ell,H'}^{(\kappa)}(F')
   \right|
   \le
   C_{\mathrm{proj}}^\star\,|V_H\setminus V_{H'}|\,\rho_\ell.
   \]

## Theorem 1 (Multi-Block Refinement Cauchy Bound)

Under (NZ4)+(RCN-H)+(BND-H), for fixed \(H\in\mathfrak H\), \(F\in\mathcal A_H^{\mathrm{nl}}\),
\[
\left|
\omega_{\eta,\ell,H}^{(\kappa)}(F)-\omega_{\eta,m,H}^{(\kappa)}(F)
\right|
\le
\left(
\frac{C_{F,H}}{z_*}+\frac{M_{F,H}C_{1,H}}{z_*^2}
\right)(\rho_\ell+\rho_m).
\]
With (COMB-H), this is uniformly controlled by graph size/edge count:
\[
\left|
\omega_{\eta,\ell,H}^{(\kappa)}(F)-\omega_{\eta,m,H}^{(\kappa)}(F)
\right|
\le
C_{\mathrm{mb}}^\star\,(1+|E_H|+|V_H|)\,(\rho_\ell+\rho_m),
\]
for explicit \(C_{\mathrm{mb}}^\star\) depending only on
\((C_F^\star,C_1^\star,M_F^\star,z_*)\).

### Proof sketch

Apply the AN-29 ratio-difference identity graph-by-graph, then substitute
(COMB-H) bounds to expose explicit dependence on \(|V_H|,|E_H|\). \(\square\)

## Theorem 2 (Projective Consistency in the Refinement Limit)

Assume Theorem 1 hypotheses plus (PROJ-H). Then:

1. for each finite \(H\), \(\omega_{\eta,\ell,H}^{(\kappa)}(F)\) converges as
   \(\ell\to\infty\) to \(\omega_{\eta,\infty,H}^{(\kappa)}(F)\);
2. for each induced subgraph \(H'\subseteq H\), the refinement-limit family is
   exactly projectively consistent:
   \[
   \omega_{\eta,\infty,H}^{(\kappa)}(F'\circ\pi_{H\to H'})
   =
   \omega_{\eta,\infty,H'}^{(\kappa)}(F');
   \]
3. if AN-29 de-regularization hypotheses hold uniformly in \(H\in\mathfrak H\),
   then \(\eta\to0^+\) commutes with these projective limits in the same class.

### Proof sketch

Take \(\ell\to\infty\) in (PROJ-H). Since \(\rho_\ell\to0\), finite-scale defects
vanish and exact projective consistency follows. De-regularization is inherited
from uniform AN-29 hypotheses. \(\square\)

## Corollary (AN-30 Scoped Upgrade)

AN-30 upgrades Claim 1 in the scoped \(d=3\) oscillatory branch:

1. nonlocal control extends from fixed two-block classes to arbitrary finite
   graph-indexed multi-block families,
2. refinement Cauchy rates now carry explicit combinatorial growth factors,
3. the refinement-limit state family is projectively consistent across induced
   graph restrictions.

Next target (AN-31): extend AN-30 from finite graph-indexed families to
uniformly locally finite exhaustion families with summability-weighted
combinatorial constants.

## Validation Contract

### Assumptions

1. AN-29 assumptions remain active, now indexed by \(H\in\mathfrak H\),
2. projective defects are explicit at finite scale via (PROJ-H).

### Units and dimensions check

1. \(\rho_\ell\) is dimensionless,
2. renormalized block coordinates \(v_{B_v}=a^{3/2}\phi|_{B_v}\) are unchanged.

### Symmetry/conservation checks

1. finite-graph indexing does not alter local lattice symmetry assumptions,
2. restriction maps \(H\to H'\) preserve observable algebra structure.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an30_multiblock_projective_consistency_check.py
```

The script checks:

1. denominator lower bounds across graph family and scales,
2. ratio Cauchy bounds with explicit graph-dependent constants,
3. finite-scale projective defects decreasing with refinement,
4. near-exact projective consistency at finest scales,
5. de-regularization stabilization in the multi-block proxy.

### Confidence statement

AN-30 is theorem-grade in this scoped lane under explicit graph-indexed rate and
projective-defect assumptions. It strengthens nonlocal structure control but does
not yet close full global continuum reconstruction.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic seed printed by script,
3. date anchor: 2026-02-09 (US).

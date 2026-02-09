# Claim 1 Phase BV (AN-29): \(d=3\) Nonlocal-Cylinder Continuum/Refinement Cauchy Control

Date: 2026-02-09 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-an28-nonlocal-cylinder-transfer.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-oscillatory-dereg-class-transfer.md`

## Goal

Close the next Claim 1 gap after AN-28 by extracting explicit refinement
Cauchy control for disconnected nonlocal cylinders in the same \(d=3\)
oscillatory/de-regularized branch, with denominator bookkeeping made explicit.

## Target/Model/Existence Declaration (Non-Drift Rule)

1. target dimension: \(d=3\),
2. model class: AN-24/AN-28 nearest-neighbor lattice \(\phi^4\), finite volume,
3. existence notion: continuum/refinement Cauchy control for AN-28 nonlocal
   observable and SD-test channels,
4. geometric \(1/2\)-density role: interpretation only.

## Setup

Fix two disjoint local blocks \(B_1,B_2\) and the AN-28 nonlocal classes
\(\mathcal A_{B_1,B_2}^{\mathrm{nl}}\), \(\mathcal T_{B_1,B_2}^{\mathrm{nl}}\).

Let \(\ell\in\mathbb N\) index refinement scale
\((a_\ell,L_\ell)\) with \(a_\ell\downarrow0,\ L_\ell\uparrow\infty\), and define
\[
\rho_\ell:=a_\ell^\alpha+L_\ell^{-\beta},\qquad \alpha,\beta>0.
\]
For \(\eta\in[0,\eta_*]\), write normalized AN-28 branch states as
\[
\omega_{\eta,\ell}^{(\kappa)}(F)=
\frac{\mathcal I_{\eta,\ell}^{(\kappa)}(F)}
{\mathcal I_{\eta,\ell}^{(\kappa)}(1)},
\qquad
c_\eta=\eta-\frac{i}{h}.
\]

## Assumption Package (AN-29)

For fixed bounded \(F\in\mathcal A_{B_1,B_2}^{\mathrm{nl}}\) and
\(\psi\in\mathcal T_{B_1,B_2}^{\mathrm{nl}}\):

1. **(NZ3)** scale-uniform denominator lower bound:
   \[
   \inf_{\eta,\ell,\kappa}
   \left|\mathcal I_{\eta,\ell}^{(\kappa)}(1)\right|\ge z_*>0.
   \]
2. **(RCN-F)** numerator Cauchy rate for \(F\):
   \[
   \left|
   \mathcal I_{\eta,\ell}^{(\kappa)}(F)
   -
   \mathcal I_{\eta,m}^{(\kappa)}(F)
   \right|
   \le C_F(\rho_\ell+\rho_m).
   \]
3. **(RCD)** denominator Cauchy rate:
   \[
   \left|
   \mathcal I_{\eta,\ell}^{(\kappa)}(1)
   -
   \mathcal I_{\eta,m}^{(\kappa)}(1)
   \right|
   \le C_1(\rho_\ell+\rho_m).
   \]
4. **(BND-F)** numerator absolute bound:
   \[
   \sup_{\eta,\ell,\kappa}
   \left|\mathcal I_{\eta,\ell}^{(\kappa)}(F)\right|
   \le M_F<\infty.
   \]
5. **(RCN-SD)** analogous Cauchy-rate assumptions for
   \(\mathcal I_{\eta,\ell}^{(\kappa)}(\partial_i\psi)\) and
   \(\mathcal I_{\eta,\ell}^{(\kappa)}(\psi\,\partial_iS)\), \(i\in B_1\).

AN-29 keeps AN-28's envelope/moment/insertion assumptions in force as the source
of these rate constants.

## Theorem 1 (Refinement Cauchy Bound for Nonlocal Ratios)

Under (NZ3)+(RCN-F)+(RCD)+(BND-F), for every \(\eta\in(0,\eta_*]\),
\[
\left|
\omega_{\eta,\ell}^{(\kappa)}(F)-\omega_{\eta,m}^{(\kappa)}(F)
\right|
\le
\left(
\frac{C_F}{z_*}+\frac{M_FC_1}{z_*^2}
\right)
(\rho_\ell+\rho_m).
\]
Hence \(\{\omega_{\eta,\ell}^{(\kappa)}(F)\}_{\ell\ge1}\) is Cauchy with explicit
rate and admits a refinement-limit state value
\(\omega_{\eta,\infty}^{(\kappa)}(F)\).

### Proof sketch

Write \(N_\ell:=\mathcal I_{\eta,\ell}^{(\kappa)}(F)\),
\(Z_\ell:=\mathcal I_{\eta,\ell}^{(\kappa)}(1)\). Then
\[
\frac{N_\ell}{Z_\ell}-\frac{N_m}{Z_m}
=
\frac{N_\ell-N_m}{Z_\ell}
+
N_m\frac{Z_m-Z_\ell}{Z_\ell Z_m}.
\]
Take absolute values and use \(|Z_\ell|,|Z_m|\ge z_*\),
\(|N_m|\le M_F\), plus (RCN-F),(RCD). \(\square\)

## Theorem 2 (Refinement SD Pass-Through + De-Regularized Limit)

Assume Theorem 1 hypotheses and (RCN-SD). Then:

1. the refinement limits
   \[
   \omega_{\eta,\infty}^{(\kappa)}(\partial_i\psi),\qquad
   \omega_{\eta,\infty}^{(\kappa)}(\psi\,\partial_iS)
   \]
   exist with explicit Cauchy rates inherited from Theorem 1.
2. the AN-28 SD identity survives refinement:
   \[
   \omega_{\eta,\infty}^{(\kappa)}(\partial_i\psi)=
   c_\eta\,
   \omega_{\eta,\infty}^{(\kappa)}(\psi\,\partial_iS),\qquad i\in B_1.
   \]
3. if the same channels are uniformly dominated in \(\eta\in[0,\eta_*]\), then
   \(\eta\to0^+\) passes to the refinement limit and
   \[
   \omega_{0,\infty}^{(\kappa)}(\partial_i\psi)=
   \left(-\frac{i}{h}\right)
   \omega_{0,\infty}^{(\kappa)}(\psi\,\partial_iS).
   \]

## Corollary (AN-29 Scoped Upgrade)

AN-29 upgrades AN-28 from finite-scale nonlocal transfer to explicit
continuum/refinement control in the same scoped \(d=3\) branch:

1. disconnected two-block nonlocal cylinders now carry refinement-rate bounds,
2. denominator bookkeeping is explicit at every scale pair,
3. SD identities persist through both refinement and de-regularization in this
   assumption-explicit lane.

Next target (AN-30): move from fixed two-block families to finite graph-indexed
multi-block nonlocal cylinders with uniform combinatorial constants and projective
consistency bookkeeping.

## Validation Contract

### Assumptions

1. AN-28 branch assumptions remain active (envelope/moment/insertion/non-vanishing),
2. refinement-rate constants are explicit in each channel.

### Units and dimensions check

1. \(\rho_\ell\) is dimensionless by construction,
2. AN-28 renormalized coordinates \(v_B=a^{3/2}\phi_B\) remain unchanged.

### Symmetry/conservation checks

1. periodic lattice symmetry assumptions are unchanged from AN-24/AN-28,
2. disconnected-block structure introduces no new local action term.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an29_nonlocal_continuum_cauchy_check.py
```

The script checks:

1. scale-uniform denominator lower bound,
2. ratio-difference bounds implied by numerator/denominator Cauchy rates,
3. observed refinement-tail Cauchy decay,
4. de-regularization stabilization in the finest-scale proxy.

### Confidence statement

AN-29 is theorem-grade in this scoped branch under explicit rate hypotheses.
It closes refinement bookkeeping for AN-28 nonlocal cylinders but does not yet
close full interacting global continuum reconstruction.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic seed printed by script,
3. date anchor: 2026-02-09 (US).

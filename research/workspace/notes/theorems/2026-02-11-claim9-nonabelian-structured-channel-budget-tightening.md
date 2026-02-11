# Claim 9 Phase AI: Structured Channel-Budget Tightening on \([\beta_0,\beta_1]\)

Date: 2026-02-11 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-11-claim9-nonabelian-adaptive-transfer-budget-window.md`
- `research/workspace/notes/theorems/2026-02-11-claim9-nonabelian-transfer-positivity-window-criterion.md`

## Goal

Tighten transfer budgets between AG coarse bounds and AH adaptive bounds by
introducing a structured channel envelope that is:

1. analytically computable from mean+fluctuation data,
2. guaranteed tighter than coarse bounds,
3. guaranteed to upper-bound the adaptive derivative envelope.

## Setup

As in AG/AH:
\[
\partial_\beta\log\langle W(r,T)\rangle_\beta
=
-a_\beta(r,T)\,rT+b_\beta(r,T)\,(r+T)+R_\beta(r,T).
\]

AG coarse budget:
\[
\Lambda_{\mathrm{coarse}}(r,T)=A_*rT+B_*(r+T)+R_*.
\]

AH adaptive budget:
\[
\Lambda_{\mathrm{adapt}}(r,T)
:=
\sup_{\beta\in[\beta_0,\beta_1]}
\left|
-a_\beta rT+b_\beta(r+T)+R_\beta
\right|.
\]

Pick structured reference channels \((\bar a,\bar b,\bar R)\) and fluctuation
envelopes \((\Sigma_a,\Sigma_b,\Sigma_R)\) such that for all \(\beta\):
\[
|a_\beta-\bar a|\le\Sigma_a,\quad
|b_\beta-\bar b|\le\Sigma_b,\quad
|R_\beta-\bar R|\le\Sigma_R.
\]

Define structured budget:
\[
\Lambda_{\mathrm{struct}}(r,T)
:=
\left|
-\bar a\,rT+\bar b\,(r+T)+\bar R
\right|
\;+\;
\Sigma_a\,rT+\Sigma_b\,(r+T)+\Sigma_R.
\]

## Theorem 1 (Budget Sandwich)

Assume additionally:
\[
|\bar a|+\Sigma_a\le A_*,\qquad
|\bar b|+\Sigma_b\le B_*,\qquad
|\bar R|+\Sigma_R\le R_*.
\]
Then for every \((r,T)\):
\[
\Lambda_{\mathrm{adapt}}(r,T)
\le
\Lambda_{\mathrm{struct}}(r,T)
\le
\Lambda_{\mathrm{coarse}}(r,T).
\]

### Proof

For fixed \(\beta\), decompose:
\[
-a_\beta rT+b_\beta(r+T)+R_\beta
=
\big(-\bar a rT+\bar b(r+T)+\bar R\big)
\;+\;
\big(-(a_\beta-\bar a)rT+(b_\beta-\bar b)(r+T)+(R_\beta-\bar R)\big).
\]
Take absolute values and apply fluctuation bounds to get
\[
\left|-a_\beta rT+b_\beta(r+T)+R_\beta\right|
\le
\Lambda_{\mathrm{struct}}(r,T).
\]
Taking sup in \(\beta\) gives
\(\Lambda_{\mathrm{adapt}}\le\Lambda_{\mathrm{struct}}\).

For the second inequality, use
\[
\left|-\bar a rT+\bar b(r+T)+\bar R\right|
\le
|\bar a|rT+|\bar b|(r+T)+|\bar R|,
\]
then add fluctuation terms and apply the three envelope constraints above to get
\(\Lambda_{\mathrm{struct}}\le\Lambda_{\mathrm{coarse}}\). \(\square\)

## Corollary (Window Ordering with Clipping)

Define safe radii:
\[
\Delta\beta_{\bullet}
:=
\inf_{(r,T)\in\mathcal W_{r,T}}
\frac{m_0(r,T)}{2\,\Lambda_{\bullet}(r,T)},
\quad
\widetilde{\Delta\beta}_{\bullet}
:=
\min\!\big(\Delta\beta_{\bullet},\,\beta_1-\beta_0\big),
\]
for \(\bullet\in\{\mathrm{coarse},\mathrm{struct},\mathrm{adapt}\}\), where
\(m_0(r,T)=-\log\langle W(r,T)\rangle_{\beta_0}>0\).

Then:
\[
\widetilde{\Delta\beta}_{\mathrm{coarse}}
\le
\widetilde{\Delta\beta}_{\mathrm{struct}}
\le
\widetilde{\Delta\beta}_{\mathrm{adapt}}.
\]

So AI yields a deterministic safe-window lift over AG while preserving AH as the
best envelope in this hierarchy.

## Validation Contract

### Assumptions

1. explicit \((G,D)=(SU(N),D)\), \(N\ge2,\ D\ge3\),
2. explicit extraction window \(\mathcal W_{r,T}\),
3. explicit reference+fluctuation envelopes with coarse-compatibility constraints.

### Units and dimensions check

1. all \(\Lambda\)-budgets and \(\Delta\beta\)-radii are dimensionless,
2. budget terms pair correctly with \(rT\), \(r+T\), and residual channels.

### Symmetry/conservation checks

1. all quantities remain gauge-invariant Wilson-loop derivative channels,
2. no gauge-dependent decomposition is introduced.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim9_nonabelian_structured_budget_tightening_check.py
```

The script verifies:

1. budget sandwich
   `Lambda_adapt <= Lambda_struct <= Lambda_coarse`,
2. clipped safe-window ordering
   `Delta_coarse <= Delta_struct <= Delta_adapt`,
3. positivity and drift-budget control inside the structured safe window.

### Confidence statement

AI is a scoped transfer-budget tightening step that improves usable safe-window
length beyond AG while retaining explicit analytic control.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic grids and parameters printed by script,
3. date anchor: 2026-02-11 (US).

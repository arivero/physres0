# Claim 9 Phase AH: Adaptive Transfer Budget for Wider Positivity Windows

Date: 2026-02-11 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-11-claim9-nonabelian-transfer-positivity-window-criterion.md`
- `research/workspace/notes/theorems/2026-02-09-claim9-nonabelian-beyond-window-transfer-assumptions.md`

## Goal

Widen the AG positivity-safe transfer interval by replacing the coarse budget
\(\Lambda(r,T)=A_*rT+B_*(r+T)+R_*\) with an adaptive derivative envelope that
tracks actual channel combinations.

## Setup

As in AG, assume
\[
\partial_\beta\log\langle W(r,T)\rangle_\beta
=
-a_\beta(r,T)\,rT+b_\beta(r,T)\,(r+T)+R_\beta(r,T),
\]
on \(\beta\in[\beta_0,\beta_1]\), with coarse bounds
\[
|a_\beta|\le A_*,\quad |b_\beta|\le B_*,\quad |R_\beta|\le R_*.
\]

Define anchor margin
\[
m_0(r,T):=-\log\langle W(r,T)\rangle_{\beta_0}>0.
\]

AG uses
\[
\Lambda_{\mathrm{coarse}}(r,T):=A_*rT+B_*(r+T)+R_*.
\]

AH introduces
\[
\Lambda_{\mathrm{adapt}}(r,T)
:=
\sup_{\beta\in[\beta_0,\beta_1]}
\left|
-a_\beta(r,T)\,rT+b_\beta(r,T)\,(r+T)+R_\beta(r,T)
\right|.
\]

By triangle inequality:
\[
\Lambda_{\mathrm{adapt}}(r,T)\le \Lambda_{\mathrm{coarse}}(r,T).
\]

## Theorem 1 (Adaptive Positivity Radius)

If \(m_0(r,T)>0\) and \(\Lambda_{\mathrm{adapt}}(r,T)<\infty\), then for each
\((r,T)\),
\[
|\beta-\beta_0|<\frac{m_0(r,T)}{\Lambda_{\mathrm{adapt}}(r,T)}
\implies
0<\langle W(r,T)\rangle_\beta<1.
\]

### Proof

Integrate derivative identity:
\[
\log\langle W\rangle_\beta-\log\langle W\rangle_{\beta_0}
=
\int_{\beta_0}^{\beta}\partial_s\log\langle W\rangle_s\,ds.
\]
Hence
\[
\left|\log\langle W\rangle_\beta-\log\langle W\rangle_{\beta_0}\right|
\le
\Lambda_{\mathrm{adapt}}(r,T)\,|\beta-\beta_0|.
\]
If the RHS is \(<m_0(r,T)\), then \(\log\langle W\rangle_\beta<0\), giving
\(0<\langle W\rangle_\beta<1\). \(\square\)

## Corollary (Uniform Safe-Window Widening vs AG)

Define
\[
\Delta\beta_{\mathrm{coarse}}
:=
\inf_{(r,T)\in\mathcal W_{r,T}}
\frac{m_0(r,T)}{2\,\Lambda_{\mathrm{coarse}}(r,T)},
\]
\[
\Delta\beta_{\mathrm{adapt}}
:=
\inf_{(r,T)\in\mathcal W_{r,T}}
\frac{m_0(r,T)}{2\,\Lambda_{\mathrm{adapt}}(r,T)}.
\]
Then
\[
\Delta\beta_{\mathrm{adapt}}\ge\Delta\beta_{\mathrm{coarse}}.
\]
Operationally on a fixed transfer interval \([\beta_0,\beta_1]\), use clipped
radii
\[
\widetilde{\Delta\beta}_{\bullet}:=
\min\!\left(\Delta\beta_{\bullet},\,\beta_1-\beta_0\right),
\]
so guaranteed windows remain inside the declared AD/AG transfer domain.

So AG's safe window is a guaranteed baseline; AH provides an equal-or-larger
window when channel combinations are less adversarial than the triangle bound.

## Validation Contract

### Assumptions

1. explicit \((G,D)=(SU(N),D)\), \(N\ge2,\ D\ge3\),
2. explicit extraction window \(\mathcal W_{r,T}\),
3. AD decomposition with coarse bounds and anchor margin data.

### Units and dimensions check

1. \(\log\langle W\rangle\), \(m_0\), \(\Lambda_{\mathrm{coarse}}\),
   \(\Lambda_{\mathrm{adapt}}\), and \(\Delta\beta\) are dimensionless.

### Symmetry/conservation checks

1. objects remain gauge-invariant Wilson-loop channels,
2. no gauge-dependent quantities are introduced.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim9_nonabelian_adaptive_transfer_window_check.py
```

The script verifies:

1. \(\Lambda_{\mathrm{adapt}}\le\Lambda_{\mathrm{coarse}}\) on a deterministic
   \((r,T)\)-grid,
2. \(\Delta\beta_{\mathrm{adapt}}\ge\Delta\beta_{\mathrm{coarse}}\),
3. positivity (`0 < W < 1`) on test points inside
   \([\beta_0,\beta_0+\Delta\beta_{\mathrm{adapt}}]\).

### Confidence statement

AH is a scoped transfer-window widening step. It does not remove AD channel
bounds, but extracts more usable window length from the same assumptions by
replacing coarse triangle budgets with adaptive derivative envelopes.
Phase AI now adds a structured-budget sandwich
(`Lambda_adapt <= Lambda_struct <= Lambda_coarse`) in
`research/workspace/notes/theorems/2026-02-11-claim9-nonabelian-structured-channel-budget-tightening.md`
to keep that widening analytically computable from channel means/fluctuations.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic grids and parameters printed by script,
3. date anchor: 2026-02-11 (US).

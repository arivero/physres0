# Claim 9 Phase AG: Positivity-Window Criterion for Beyond-Window Transfer

Date: 2026-02-11 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim9-nonabelian-beyond-window-transfer-assumptions.md`
- `research/workspace/notes/theorems/2026-02-09-claim9-nonabelian-derivative-covariance-criterion.md`
- `research/workspace/notes/theorems/2026-02-09-claim9-nonabelian-firstprinciples-transfer-clustering.md`

## Goal

Replace AD's standalone transfer assumption `(TB-POS)` by an explicit admissible
`beta`-window inequality in one fixed \((SU(N),D)\) extraction window.

This is an assumption-elimination upgrade:
positivity is derived from anchor data plus transfer-channel bounds, instead of
being postulated for the whole transfer interval.

## Dependency Declaration

\[
\mathrm{C9\text{-}NA}(G,D)=\mathrm{C9\text{-}NA}(SU(N),D),\qquad N\ge2,\ D\ge3.
\]

## Setup

Use AD transfer decomposition on a fixed extraction window
\(\mathcal W_{r,T}\subset\mathbb R_{>0}^2\):
\[
\partial_\beta\log\langle W(r,T)\rangle_\beta
=
-a_\beta(r,T)\,rT+b_\beta(r,T)\,(r+T)+R_\beta(r,T),
\]
with bounds
\[
|a_\beta(r,T)|\le A_*,\quad
|b_\beta(r,T)|\le B_*,\quad
|R_\beta(r,T)|\le R_*.
\]

Define at anchor \(\beta_0\):
\[
m_0(r,T):=-\log\langle W(r,T)\rangle_{\beta_0}>0,
\]
and the transfer budget
\[
\Lambda(r,T):=A_*\,rT+B_*\,(r+T)+R_*.
\]

## Theorem 1 (Positivity from Anchor Margin)

Assume:

1. AD decomposition and bounds above hold on \([\beta_0,\beta_1]\),
2. anchor margin \(m_0(r,T)>0\) on \(\mathcal W_{r,T}\).

Then for any \((r,T)\in\mathcal W_{r,T}\) and any \(\beta\) satisfying
\[
|\beta-\beta_0|<\frac{m_0(r,T)}{\Lambda(r,T)},
\]
one has
\[
0<\langle W(r,T)\rangle_\beta<1.
\]

### Proof

Integrate the derivative identity from \(\beta_0\) to \(\beta\):
\[
\log\langle W\rangle_\beta-\log\langle W\rangle_{\beta_0}
=\int_{\beta_0}^{\beta}
\left(-a_s rT+b_s(r+T)+R_s\right)\,ds.
\]
Taking absolute values and bounds gives
\[
\left|\log\langle W\rangle_\beta-\log\langle W\rangle_{\beta_0}\right|
\le \Lambda(r,T)\,|\beta-\beta_0|.
\]
Hence
\[
\log\langle W\rangle_\beta
\le
-m_0(r,T)+\Lambda(r,T)|\beta-\beta_0|<0.
\]
So \(\langle W\rangle_\beta=e^{\log\langle W\rangle_\beta}\) is strictly positive
and strictly below 1. \(\square\)

## Corollary (AD Package with `(TB-POS)` Removed)

Define a uniform admissible radius over the extraction window:
\[
\Delta\beta_{\mathrm{safe}}
:=
\inf_{(r,T)\in\mathcal W_{r,T}}
\frac{m_0(r,T)}{2\,\Lambda(r,T)}.
\]
If \(\Delta\beta_{\mathrm{safe}}>0\), then on
\([\beta_0,\beta_0+\Delta\beta_{\mathrm{safe}}]\) positivity is guaranteed by
Theorem 1 and `(TB-POS)` is no longer an independent transfer assumption.

Interpretation:

1. AD now needs `(TB-DIFF)+(TB-BOUNDS)` plus anchor margin data,
2. positivity is converted into a computable admissibility gate.

## Validation Contract

### Assumptions

1. explicit \((G,D)=(SU(N),D)\), \(N\ge2,\ D\ge3\),
2. explicit extraction window \(\mathcal W_{r,T}\),
3. explicit anchor margin map \(m_0(r,T)\),
4. explicit channel bounds \(A_*,B_*,R_*\) (from AD/AE/AF lane).

### Units and dimensions check

1. \(\log\langle W\rangle\) and \(m_0\) are dimensionless,
2. \(\Lambda\) multiplies \(|\beta-\beta_0|\) to a dimensionless drift,
3. \(\Delta\beta_{\mathrm{safe}}\) is dimensionless.

### Symmetry/conservation checks

1. all statements are on gauge-invariant Wilson-loop expectations,
2. no gauge-fixing dependent object is introduced.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim9_nonabelian_transfer_positivity_window_check.py
```

The script verifies:

1. budget inequality
   `|logW(beta)-logW(beta0)| <= Lambda(r,T)*|beta-beta0|`,
2. positivity (`0 < W < 1`) for all \(\beta\) inside the computed safe window,
3. exact transfer identities remain compatible with AD channel decomposition.

### Confidence statement

AG is a scoped assumption-elimination step: it removes `(TB-POS)` as a free
assumption in the verified transfer subwindow. Remaining open work is to widen
that subwindow by improving first-principles \(A_*,B_*,R_*\) controls and then
close the dynamical-matter string-breaking crossover lane.
Phase AH now provides an adaptive-budget widening step in the same transfer lane
(`research/workspace/notes/theorems/2026-02-11-claim9-nonabelian-adaptive-transfer-budget-window.md`).

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic seed printed by script,
3. date anchor: 2026-02-11 (US).

# Claim 9 Phase AJ: Segmented Structured-Budget Transfer Cover on Full Window

Date: 2026-02-11 (US)
Depends on:
- `research/workspace/notes/theorems/2026-02-11-claim9-nonabelian-structured-channel-budget-tightening.md`

## Goal

Go beyond single-anchor clipped windows (AG/AH/AI) by constructing a segmented
transfer proof that can cover the full interval `[
\beta_0,\beta_1]` with local structured budgets.

## Setup

For each fixed Wilson loop geometry `(r,T)`:
\[
\partial_\beta \log\langle W\rangle_\beta = D_\beta(r,T).
\]
Partition
\[
\beta_0 = \beta^{(0)} < \beta^{(1)} < \cdots < \beta^{(J)} = \beta_1,
\qquad
h_j := \beta^{(j+1)}-\beta^{(j)}.
\]

For each segment `j`, assume a structured local envelope
\[
|D_\beta(r,T)| \le \Lambda_j(r,T),
\qquad \beta\in[\beta^{(j)},\beta^{(j+1)}].
\]
Define segment anchor margin
\[
m_j(r,T):=-\log\langle W(r,T)\rangle_{\beta^{(j)}} > 0,
\]
and safe radius
\[
\Delta_j := \inf_{(r,T)\in\mathcal W_{r,T}} \frac{m_j(r,T)}{2\Lambda_j(r,T)}.
\]

## Theorem 1 (Segment Step Safety)

If `h_j <= \Delta_j`, then for all `(r,T)` in the extraction window:
\[
-\log\langle W(r,T)\rangle_{\beta^{(j+1)}}
\ge
\frac12 m_j(r,T)
>0.
\]
Hence positivity/nontriviality is preserved at the next anchor.

### Proof

Integrating derivative bound:
\[
\left|\log\langle W\rangle_{\beta^{(j+1)}}-
\log\langle W\rangle_{\beta^{(j)}}\right|
\le \Lambda_j h_j
\le \frac12 m_j.
\]
With `\log\langle W\rangle_{\beta^{(j)}}=-m_j`, we obtain
\[
\log\langle W\rangle_{\beta^{(j+1)}} \le -\frac12 m_j,
\]
which is equivalent to the claim. \(\square\)

## Theorem 2 (Full-Window Cover by Induction)

If every segment satisfies `h_j <= \Delta_j`, then positivity propagates from
`\beta_0` to all anchors `\beta^{(j)}` and therefore over the whole interval
`[\beta_0,\beta_1]` by concatenation.

This yields a constructive full-window certification criterion using only local
structured envelopes.

## Corollary (Adaptive Mesh Rule)

Given local budgets `\Lambda_j`, choose `h_j` with a fixed safety factor
`0<\theta<1`:
\[
h_j \le \theta\,\Delta_j.
\]
Then the number of segments required for full-window cover is finite whenever
`\Delta_j` has a positive lower bound on the propagated anchors.

## Validation Contract

### Assumptions

1. fixed non-Abelian model/extraction window as in AG/AH/AI,
2. local structured derivative envelopes on each segment,
3. positive initial anchor margins at `\beta_0`.

### Units and dimensions check

1. `\beta`, `h_j`, and `\Delta_j` are dimensionless,
2. `\Lambda_j` and `m_j` are dimensionless derivative/margin channels.

### Symmetry/conservation checks

1. all bounds are stated on gauge-invariant Wilson-loop observables,
2. no gauge-dependent decomposition is introduced.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim9_nonabelian_segmented_transfer_cover_check.py
```

The script verifies existence of a finite segment count `J_*` covering full
`[\beta_0,\beta_1]` and checks positivity preservation at each propagated anchor.

### Confidence statement

AJ is a scoped but meaningful step toward first-principles beyond-window control:
it converts one-shot clipped radii into a finite constructive cover criterion.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic interval partition search,
3. date anchor: 2026-02-11 (US).

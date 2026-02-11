# Claim 9 Phase AK: Segment Lipschitz-Budget Bridge (Analytic Sup Bound)

Date: 2026-02-11 (US)
Depends on:
- `research/workspace/notes/theorems/2026-02-11-claim9-segmented-transfer-window-cover.md`

## Goal

Reduce AJ's dependence on dense segment sampling by introducing an analytic
Lipschitz-based segment budget bound.

## Setup

On a segment `I_j=[beta_j,beta_{j+1}]` of length `h_j`, define derivative channel
\[
D_\beta(r,T):=\partial_\beta \log\langle W(r,T)\rangle_\beta.
\]
Assume `D_beta` is Lipschitz on `I_j` with constant `L_j(r,T)`:
\[
|D_{\beta_1}-D_{\beta_2}|\le L_j(r,T)|\beta_1-\beta_2|.
\]

Define endpoint envelope
\[
E_j(r,T):=\max\big(|D_{\beta_j}(r,T)|, |D_{\beta_{j+1}}(r,T)|\big).
\]

## Theorem (Analytic Segment Sup Budget)

For every `beta in I_j`:
\[
|D_\beta(r,T)|
\le
E_j(r,T) + L_j(r,T) h_j.
\]
Hence the AJ segment budget can be chosen analytically as
\[
\Lambda_j^{\mathrm{Lip}}(r,T):=E_j(r,T)+L_j(r,T)h_j,
\]
which guarantees
\[
\sup_{\beta\in I_j}|D_\beta(r,T)|\le\Lambda_j^{\mathrm{Lip}}(r,T).
\]

### Proof

For any `beta in I_j`, pick nearest endpoint `beta_* in {beta_j,beta_{j+1}}`.
Then `|beta-beta_*|<=h_j`. Lipschitz bound gives
\[
|D_\beta|\le |D_{\beta_*}| + L_j|\beta-\beta_*|
\le E_j + L_j h_j.
\]
\(\square\)

## Corollary (AJ without Dense Sup Scans)

Replacing sampled sup budgets by `Lambda_j^{Lip}` keeps AJ's segment-step safety
proof valid while using only endpoint derivatives and Lipschitz constants.

## Validation Contract

### Assumptions

1. gauge-invariant derivative channel `D_beta` on each segment,
2. segment-wise Lipschitz constants available,
3. AJ positivity-transfer framework unchanged.

### Units and dimensions check

1. `D_beta`, `E_j`, and `Lambda_j^{Lip}` are dimensionless,
2. `L_j h_j` is dimensionless.

### Symmetry/conservation checks

1. no gauge-dependent decomposition introduced,
2. transfer remains within Wilson-loop gauge-invariant sector.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim9_nonabelian_segment_lipschitz_budget_check.py
```

The script verifies `sup_abs_D <= Lambda_lip` on deterministic segment grids and
compares `Lambda_lip` to sampled sup envelopes.

### Confidence statement

AK is a scoped analytic tightening step that removes sampling dependence from the
segment budget definition while preserving AJ safety guarantees.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic segment/radius grid and analytic derivatives,
3. date anchor: 2026-02-11 (US).

# Claim 1 Phase CC (AN-33L-B): Lean Projective-Defect and De-Regularization Transfer

Date: 2026-02-10 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-10-claim1-d3-an33l-an34l-exhaustion-transfer-lean-bridge.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-an31-exhaustion-summability-lift.md`
- `research/workspace/proofs/Claim1lean/WeightedLocalGraphDecay.lean`

## Goal

Close AN-33L-B by proving machine-checked transfer lemmas that:

1. move projective-defect bounds across regularization channels,
2. transfer pairwise exhaustion rates from regularized to de-regularized channels.

## Target/Model/Existence Declaration (Non-Drift Rule)

1. target dimension: \(d=3\),
2. model class: AN-31/AN-34 scoped oscillatory/de-regularized branch,
3. existence notion: exhaustion-indexed Cauchy/projective bookkeeping transfer (support lane),
4. geometric \(1/2\)-density role: interpretation only.

## Lean Additions (Machine-Checked)

In `Claim1lean/WeightedLocalGraphDecay.lean`:

1. `abs_le_add_of_abs_sub_le`:
   \[
   |x-y|\le e,\ |y|\le b \Longrightarrow |x|\le e+b.
   \]
2. `projective_defect_transfer_of_regularization`:
   if \(|\delta_0(n)-\delta_\eta(n)|\le Be\) and
   \(|\delta_\eta(n)|\le A\,t_n\), then
   \[
   |\delta_0(n)|\le A\,t_n + Be.
   \]
3. `pairwise_transfer_bound_of_regularization`:
   if \(|u_0(n)-u_\eta(n)|\le Be\) and
   \[
   |u_\eta(n)-u_\eta(m)|\le A(t_n+t_m),
   \]
   then
   \[
   |u_0(n)-u_0(m)|\le A(t_n+t_m)+2Be.
   \]
4. `pairwise_transfer_bound_between_regularizations`:
   with reference channel \(u_{\mathrm{ref}}\),
   \[
   |u_\eta(n)-u_{\mathrm{ref}}(n)|\le Be_\eta,\quad
   |u_{\eta'}(n)-u_{\mathrm{ref}}(n)|\le Be_{\eta'},
   \]
   and pairwise reference rate \(A(t_n+t_m)\), one gets
   \[
   |u_\eta(n)-u_{\eta'}(m)|
   \le
   A(t_n+t_m)+Be_\eta+Be_{\eta'}.
   \]

## Consequence for AN-31/AN-34 Interfaces

These lemmas provide an explicit transfer template:

1. AN-31 projective-defect envelopes proved in a regularized lane can be moved
   to de-regularized bookkeeping with additive \(Be\)-type terms,
2. AN-34 pairwise ratio rates can be transferred across \(\eta\)-channels with
   explicit penalties and without changing tail constants \(A\).

## Proof Sketch

All lemmas are triangle-inequality decompositions on top of the AN-33L/AN-34L-A
pairwise wrappers, now machine-checked for direct reuse. \(\square\)

## Validation Contract

### Assumptions

1. regularization mismatch bounds are explicit,
2. pairwise tail-rate and/or projective-defect envelopes are explicit.

### Units and dimensions check

1. \(t_n\), \(e\), \(e_\eta\), \(e_{\eta'}\) are dimensionless bookkeeping terms,
2. transfer constants remain dimensionless.

### Symmetry/conservation checks

1. no new symmetry assumptions are introduced,
2. transfer is algebraic and compatible with existing AN-31/AN-34 hypotheses.

### Independent cross-check path

Run:

```bash
cd research/workspace/proofs
/Users/arivero/.elan/bin/lake build Claim1lean.WeightedLocalGraphDecay
```

### Confidence statement

AN-33L-B is machine-checked and closes the requested projective-defect and
de-regularization transfer step at the support-lane level. The commuting-limit
wrapper is now closed in AN-33L-C (see
`research/workspace/notes/theorems/2026-02-10-claim1-d3-an33l-c-commuting-limit-wrapper-lean.md`).

### Reproducibility metadata

1. Lean toolchain: `/Users/arivero/.elan/bin/lean`, `/Users/arivero/.elan/bin/lake`,
2. build command listed above,
3. date anchor: 2026-02-10 (US).

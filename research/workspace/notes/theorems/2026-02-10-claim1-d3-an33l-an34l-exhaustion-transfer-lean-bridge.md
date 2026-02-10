# Claim 1 Phase CB (AN-33L/AN-34L-A): Exhaustion-Level Lean Transfer Bridge

Date: 2026-02-10 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-an31-exhaustion-summability-lift.md`
- `research/workspace/notes/theorems/2026-02-10-claim1-d3-an34-firstprinciples-tail-rate-transmutation.md`
- `research/workspace/proofs/Claim1lean/WeightedLocalGraphDecay.lean`

## Goal

Execute the first AN-33L/AN-34L continuation step:

1. lift AN-34A one-sided tail envelopes to exhaustion-indexed pairwise rates,
2. provide field-facing transfer lemmas for AN-31 projective/Cauchy bookkeeping.

## Target/Model/Existence Declaration (Non-Drift Rule)

1. target dimension: \(d=3\),
2. model class: AN-24/AN-31/AN-34 scoped oscillatory/de-regularized lattice branch,
3. existence notion: exhaustion-indexed pairwise quantitative control feeding AN-31 Cauchy/projective limits,
4. geometric \(1/2\)-density role: interpretation only.

## Lean Transfer Package (Machine-Checked)

In `Claim1lean/WeightedLocalGraphDecay.lean`:

1. `pairwise_tail_rate_of_exhaustion_envelope`:
   \[
   |u_n-u_\infty|\le A\,t_n\ \forall n
   \Longrightarrow
   |u_n-u_m|\le A\,(t_n+t_m).
   \]
2. `pairwise_add_rate_of_exhaustion_envelopes`:
   two one-sided envelopes for \(u_n,v_n\) imply an additive pairwise envelope
   for \((u_n+v_n)\) with constant \(A_u+A_v\).
3. `pairwise_ratio_rate_of_exhaustion_envelopes`:
   one-sided numerator/denominator envelopes plus denominator floor imply
   \[
   \left|\frac{N_n}{D_n}-\frac{N_m}{D_m}\right|
   \le
   \left(\frac{A_N}{d_0}+\frac{B A_D}{d_0^2}\right)\!(t_n+t_m),
   \]
   matching AN-34A constants in exhaustion-indexed form.

## Field-Facing Transfer Consequence

Under AN-31 tail controls \(t_n=W_n^{\mathrm{tail}}\), these wrappers turn
one-sided envelopes into the exact pairwise structure required by:

1. AN-31 Cauchy bookkeeping on exhaustion levels,
2. AN-31 projective-defect splitting via additive envelopes,
3. AN-34 ratio-state rate control in exhaustion-indexed form.

## Proof Sketch

Each wrapper is a direct Lean corollary of the AN-34 finite wrappers:

1. `pairwise_tail_rate_of_exhaustion_envelope` uses
   `abs_sub_le_of_tail_to_limit`,
2. additive transfer applies triangle control to item 1,
3. ratio transfer applies
   `ratio_diff_bound_of_limit_tail_rates` pointwise in indices \((n,m)\).
\(\square\)

## Validation Contract

### Assumptions

1. one-sided tail envelopes are explicit at each exhaustion level,
2. denominator floor and numerator-size bounds are explicit where ratio control is used.

### Units and dimensions check

1. \(t_n\) (tail envelope weights) are dimensionless bookkeeping parameters,
2. ratio-rate constants are dimensionless.

### Symmetry/conservation checks

1. no model symmetry assumptions are altered,
2. transfer is algebraic/analytic and index-structural only.

### Independent cross-check path

Run:

```bash
cd research/workspace/proofs
/Users/arivero/.elan/bin/lake build Claim1lean.WeightedLocalGraphDecay
```

### Confidence statement

AN-33L/AN-34L-A is machine-checked and closes the requested transfer bridge from
one-sided tail envelopes to AN-31-style pairwise exhaustion rates in the scoped
branch. Full projective-limit/de-regularization discharge remains the next
support-lane step (AN-33L-B).

### Reproducibility metadata

1. Lean toolchain: `/Users/arivero/.elan/bin/lean`, `/Users/arivero/.elan/bin/lake`,
2. build command listed above,
3. date anchor: 2026-02-10 (US).

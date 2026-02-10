# Claim 1 Phase BY-L/CB-L/CC-L/CD-L (AN-32L/AN-33L/AN-34L): Lean Weighted-Local and Graph-Decay Bridge

Date: 2026-02-10 (US)  
Lean module: `research/workspace/proofs/Claim1lean/WeightedLocalGraphDecay.lean`

## Goal

Close the AN-32 Lean support lane (and AN-33L/AN-34L follow-up wrappers) with
finite and exhaustion-indexed surrogate lemmas that directly support the
AN-33/AN-34 nonlocal weighted-local extension:

1. weighted-local truncation tails,
2. graph-decay nonlocal channel bounds,
3. denominator-rate ratio bookkeeping,
4. first-principles shell-tail to pairwise-rate transmutation,
5. field-facing transfer to AN-31-style exhaustion bookkeeping,
6. projective-defect/de-regularization transfer wrappers (AN-33L-B).
7. commuting-limit wrapper (AN-33L-C).

## Formalized Objects

For finite index classes:

1. `weightedL1`:
   \[
   \|x\|_{w,1}:=\sum_i |w_i|\,|x_i|.
   \]
2. `weightedTailL1`:
   \[
   \|x\|_{w,\mathrm{tail}(\chi)}:=\sum_i (1-\chi_i)|w_i|\,|x_i|.
   \]
3. exhaustion-indexed channels:
   \[
   u_n,\ N_n,\ D_n,\ t_n,\qquad n\in\mathbb N,
   \]
   used to transport one-sided tail envelopes to pairwise projective-rate bounds.

## Machine-Checked Results

1. `weightedTailL1_le_of_uniform_bound`:
   if \(|x_i|\le M\) and \(0\le \chi_i\le1\), then
   \[
   \|x\|_{w,\mathrm{tail}(\chi)}
   \le
   M\sum_i (1-\chi_i)|w_i|.
   \]
2. `weightedL1_image_le_of_column_decay`:
   for a finite nonlocal channel \(K_{ij}\), if
   \[
   \sum_i |v_i|\,|K_{ij}|\le C|w_j| \quad \forall j,
   \]
   then
   \[
   \sum_i |v_i|\Big|\sum_j K_{ij}x_j\Big|
   \le
   C\sum_j |w_j|\,|x_j|.
   \]
3. `abs_inv_sub_inv_le_of_abs_sub_le`:
   lower-bounded denominators and a denominator-difference bound imply an
   explicit reciprocal-difference rate:
   \[
   \Big|\frac1D-\frac1{D'}\Big|
   \le
   \frac{\varepsilon_D}{d_0^2}.
   \]
4. `ratio_diff_bound_of_num_and_reciprocal_rate`:
   numerator and reciprocal-rate control imply ratio-difference control.
5. `ratio_diff_bound_of_denominator_rates`:
   denominator-rate bookkeeping is propagated to ratio-state error bounds.
6. `abs_sub_le_add_of_dist_to_center`:
   pairwise difference is controlled by one-sided distances to a common center.
7. `abs_sub_le_of_tail_to_limit`:
   one-sided tail-to-limit bounds are converted into pairwise tail-rate bounds.
8. `ratio_diff_bound_of_tail_rates`:
   pairwise numerator/denominator tail-rate control yields ratio-rate bounds.
9. `ratio_diff_bound_of_limit_tail_rates`:
   one-sided tail-to-limit envelopes are converted directly into pairwise
   ratio-rate bounds through item 7 and item 8.
10. `pairwise_tail_rate_of_exhaustion_envelope`:
    if
    \[
    |u_n-u_\infty|\le A\,t_n,
    \]
    then
    \[
    |u_n-u_m|\le A\,(t_n+t_m).
    \]
11. `pairwise_add_rate_of_exhaustion_envelopes`:
    two one-sided envelopes for \(u_n\) and \(v_n\) imply an additive
    pairwise-rate envelope for \(u_n+v_n\), with constant \(A_u+A_v\).
12. `pairwise_ratio_rate_of_exhaustion_envelopes`:
    one-sided numerator/denominator tail envelopes plus denominator floor imply
    pairwise ratio-rate bounds for \(N_n/D_n\) with explicit AN-34 constants.
13. `abs_le_add_of_abs_sub_le`:
    transports bounds from a reference channel to a target channel.
14. `projective_defect_transfer_of_regularization`:
    regularized projective-defect envelope + mismatch bound implies de-regularized
    projective-defect envelope.
15. `pairwise_transfer_bound_of_regularization`:
    pairwise regularized tail-rate bound transfers to de-regularized channel with
    explicit additive mismatch penalty \(2Be\).
16. `pairwise_transfer_bound_between_regularizations`:
    pairwise bound transfer between two regularization levels \(\eta,\eta'\)
    through a common reference channel.
17. `commuting_limit_of_exhaustion_and_regularization_envelopes`:
    a single abstract wrapper that combines:
    - exhaustion tail-to-limit envelopes,
    - regularization-limit proxy Cauchy envelopes,
    into joint convergence \((k,n)\to\infty\) (exhaustion + de-regularization).

## Why It Matters for AN-31/AN-33/AN-34

These lemmas give a machine-checked finite backbone for:

1. nonlocal weighted-local graph-decay estimates (AN-33 observable channel),
2. explicit denominator-rate propagation in normalized state differences,
3. AN-34A first-principles tail-to-rate transmutation in the scoped \(d=3\) lane,
4. direct transfer of those rates to AN-31-style exhaustion-indexed pairwise
   bookkeeping (AN-33L/AN-34L-A),
5. projective-defect and de-regularization transfer with explicit additive
   mismatch terms (AN-33L-B),
6. commuting-limit control for exhaustion vs de-regularization (AN-33L-C).

## Build Check

```bash
cd research/workspace/proofs
/Users/arivero/.elan/bin/lake build Claim1lean.WeightedLocalGraphDecay
```

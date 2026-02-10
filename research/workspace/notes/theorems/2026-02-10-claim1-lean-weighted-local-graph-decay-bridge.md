# Claim 1 Phase BY-L (AN-32L): Lean Weighted-Local and Graph-Decay Bridge

Date: 2026-02-10 (US)  
Lean module: `research/workspace/proofs/Claim1lean/WeightedLocalGraphDecay.lean`

## Goal

Close the AN-32 Lean support lane with finite surrogate lemmas that directly
support the AN-33 nonlocal weighted-local extension:

1. weighted-local truncation tails,
2. graph-decay nonlocal channel bounds,
3. denominator-rate ratio bookkeeping.

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

## Why It Matters for AN-33

These lemmas give a machine-checked finite backbone for:

1. nonlocal weighted-local graph-decay estimates (AN-33 observable channel),
2. explicit denominator-rate propagation in normalized state differences,
3. the next uplift to exhaustion/projective families (AN-33L target).

## Build Check

```bash
cd research/workspace/proofs
/Users/arivero/.elan/bin/lake build Claim1lean.WeightedLocalGraphDecay
```

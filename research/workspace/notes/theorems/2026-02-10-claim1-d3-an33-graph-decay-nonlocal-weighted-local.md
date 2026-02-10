# Claim 1 Phase BZ (AN-33) Draft Skeleton: \(d=3\) Graph-Decay Nonlocal Weighted-Local Lift

Date: 2026-02-10 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-10-claim1-d3-an32-weighted-local-sdtest-lift.md`
- `research/workspace/notes/theorems/2026-02-10-claim1-lean-weighted-local-graph-decay-bridge.md`
- `research/workspace/proofs/Claim1lean/WeightedLocalGraphDecay.lean`

## Goal

Draft the AN-33 theorem skeleton that extends AN-32 weighted-local
observable/SD-test classes to graph-decay nonlocal weighted-local channels with
explicit denominator-rate bookkeeping in the same scoped \(d=3\) branch.

Status in this note: statement/proof skeleton + Lean-obligation map.  
Closure is now completed in:
`research/workspace/notes/theorems/2026-02-10-claim1-d3-an33b-graph-decay-denominator-closure.md`.

## Target/Model/Existence Declaration (Non-Drift Rule)

1. target dimension: \(d=3\),
2. model class: AN-24/AN-32 nearest-neighbor lattice \(\phi^4\), scoped oscillatory/de-regularized branch,
3. existence notion: exhaustion-limit existence + SD pass-through + normalized-state Cauchy control for graph-decay weighted-nonlocal channels,
4. geometric \(1/2\)-density role: interpretation only.

## Setup (AN-33 Channel Layer)

Keep AN-32 exhaustion data \(H_n\uparrow H_\infty\), weights \(w(v)\), and tails
\(W_n^{\mathrm{tail}}\to0\).

For a finite surrogate of \(V(H_\infty)\), introduce a nonlocal kernel channel
\(K\) and weighted seminorm
\[
\|x\|_{w,1}:=\sum_v |w(v)|\,|x_v|.
\]

Model AN-33 graph-decay via column envelope:
\[
\sum_{u}|a_u|\,|K_{u v}| \le C_{\mathrm{gd}}\,w(v)\quad\forall v.
\]

This is the finite surrogate used by
`weightedL1_image_le_of_column_decay`.

Define weighted-local tails through cutoff profiles \(\chi_r\in[0,1]\):
\[
\mathrm{Tail}_{\chi_r}(x):=\sum_v (1-\chi_r(v))|w(v)|\,|x_v|,
\]
modeled by `weightedTailL1`.

## AN-33 Assumption Skeleton

1. **(AN32-UNI)** AN-32 hypotheses remain valid in the same branch.
2. **(GD-COL)** graph-decay column envelope for nonlocal kernels as above.
3. **(LOC-ENV)** local building-block envelopes from AN-32 (`OBS-UNI`, `DER-UNI`, `INS-UNI`) hold uniformly.
4. **(TAIL-TRUNC)** truncation profile \(\chi_r\) has vanishing weighted tails.
5. **(DEN-FLOOR)** normalized denominators satisfy
   \[
   |D_n(\eta,\kappa)|\ge d_0>0
   \]
   uniformly on working parameter windows.
6. **(DEN-RATE)** denominator differences satisfy explicit rates
   \[
   |D_n-D_m|\le \varepsilon_D(n,m),\qquad \varepsilon_D(n,m)\to0.
   \]
7. **(NUM-RATE)** corresponding numerator differences satisfy
   \[
   |N_n(F)-N_m(F)|\le \varepsilon_N^F(n,m),\qquad \varepsilon_N^F(n,m)\to0.
   \]
8. **(NUM-BOUND)** one side of numerators has a uniform envelope
   \[
   |N_m(F)|\le B_F.
   \]

## Theorem Skeletons

## Theorem 1 (Graph-Decay Weighted-Local Operator Control)

Under (GD-COL), for finite-surrogate channel data:
\[
\sum_u |a_u|\Big|\sum_v K_{u v}x_v\Big|
\le
C_{\mathrm{gd}}\sum_v |w(v)|\,|x_v|.
\]

Role: transfers local weighted envelopes into nonlocal weighted envelopes.

## Theorem 2 (Weighted Truncation-Tail Control)

Under (TAIL-TRUNC) and local uniform bound \(|x_v|\le M\):
\[
\mathrm{Tail}_{\chi_r}(x)
\le
M\sum_v (1-\chi_r(v))|w(v)|
\xrightarrow[r\to\infty]{}0.
\]

Role: turns nonlocal weighted-local truncations into explicit \(r\)-tail rates.

## Theorem 3 (Denominator-Rate Normalized-State Cauchy Template)

For \(R_n(F):=N_n(F)/D_n\), assumptions (DEN-FLOOR)+(DEN-RATE)+(NUM-RATE)+(NUM-BOUND)
yield
\[
|R_n(F)-R_m(F)|
\le
\frac{\varepsilon_N^F(n,m)}{d_0}
+ B_F\frac{\varepsilon_D(n,m)}{d_0^2}.
\]

Role: explicit normalized-state error splitting into numerator and denominator
rates for AN-33 nonlocal channels.

## Corollary Skeleton (AN-33 Upgrade Shape)

Combine Theorems 1-3 with AN-32 exhaustion/SD pass-through:

1. nonlocal graph-decay weighted-local observables/tests have exhaustion Cauchy limits,
2. SD pass-through extends with explicit nonlocal tail truncation control,
3. denominator-rate bookkeeping is explicit at normalized-state level and
   compatible with de-regularization/exhaustion order (under uniform AN-32/AN-33 assumptions).

## Lean Support Map (AN-32L -> AN-33 Obligations)

1. **Obligation O1 (nonlocal operator envelope)**  
   Lean lemma: `weightedL1_image_le_of_column_decay`  
   Usage: (GD-COL) -> nonlocal weighted norm bound (Theorem 1 skeleton).

2. **Obligation O2 (truncation tail vanishing)**  
   Lean lemma: `weightedTailL1_le_of_uniform_bound`  
   Usage: local uniform envelope + profile tails -> explicit truncation rate
   (Theorem 2 skeleton).

3. **Obligation O3 (reciprocal denominator control)**  
   Lean lemma: `abs_inv_sub_inv_le_of_abs_sub_le`  
   Usage: (DEN-FLOOR)+(DEN-RATE) -> \(|1/D_n-1/D_m|\) rate.

4. **Obligation O4 (ratio split with reciprocal-rate input)**  
   Lean lemma: `ratio_diff_bound_of_num_and_reciprocal_rate`  
   Usage: combine numerator rate and reciprocal denominator rate.

5. **Obligation O5 (final denominator-rate ratio bound)**  
   Lean lemma: `ratio_diff_bound_of_denominator_rates`  
   Usage: direct bound for Theorem 3 skeleton.

## Remaining Gaps to Close for Full AN-33 Claim

1. translate finite-surrogate kernel/weight conditions to exhaustion-indexed
   field blocks with explicit \(n,m,r\)-uniform constants,
2. verify denominator-rate hypotheses in the scoped oscillatory/de-regularized
   branch from AN-29/AN-30 bookkeeping data,
3. complete SD-test-side nonlocal insertion-tail closure beyond the AN-32 local
   insertion channel.

## Validation Contract

### Assumptions

1. AN-32 assumptions remain active,
2. graph-decay kernel and denominator-rate hypotheses are explicit,
3. this note is a draft skeleton, not a completed theorem closure.

### Units and dimensions check

1. weighted seminorms/tails are dimensionless bookkeeping quantities,
2. denominator-rate bounds are dimensionless ratio controls.

### Symmetry/conservation checks

1. no new symmetry-breaking regulator is introduced relative to AN-32,
2. restriction/projective maps are unchanged; only channel class is widened.

### Independent cross-check path

1. Lean module build (machine-checked finite surrogate):
   ```bash
   cd research/workspace/proofs
   /Users/arivero/.elan/bin/lake build Claim1lean.WeightedLocalGraphDecay
   ```
2. theorem-note cross-check: map each AN-33 obligation to one Lean lemma in the
   table above.

### Confidence statement

High confidence for the finite Lean support map (AN-32L).  
Medium confidence for full AN-33 closure pending field-level transfer of kernel
and denominator-rate hypotheses.

### Reproducibility metadata

1. Date anchor: 2026-02-10 (US),
2. Lean: `/Users/arivero/.elan/bin/lean` (toolchain v4.27.0 via workspace),
3. Build command log:
   - `/Users/arivero/.elan/bin/lake build Claim1lean.WeightedLocalGraphDecay`,
   - `/Users/arivero/.elan/bin/lake build Claim1lean`.

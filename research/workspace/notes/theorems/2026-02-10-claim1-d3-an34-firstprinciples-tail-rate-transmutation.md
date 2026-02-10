# Claim 1 Phase CA (AN-34A): \(d=3\) First-Principles Tail-to-Rate Transmutation

Date: 2026-02-10 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-10-claim1-d3-an33b-graph-decay-denominator-closure.md`
- `research/workspace/notes/theorems/2026-02-10-claim1-lean-weighted-local-graph-decay-bridge.md`
- `research/workspace/proofs/Claim1lean/WeightedLocalGraphDecay.lean`

## Goal

Execute the first AN-34 step: replace AN-33 denominator/numerator rate
assumptions by first-principles shell-tail bounds, then push those directly to
normalized ratio Cauchy bounds.

## Target/Model/Existence Declaration (Non-Drift Rule)

1. target dimension: \(d=3\),
2. model class: AN-24/AN-33 nearest-neighbor lattice \(\phi^4\), scoped oscillatory/de-regularized branch,
3. existence notion: exhaustion-limit normalized Cauchy control with rates derived from shell-tail summability (not postulated),
4. geometric \(1/2\)-density role: interpretation only.

## Shell-Tail Setup

Let \(\sigma_j\ge0\) be shell weights with
\[
\sum_{j\ge1}\sigma_j<\infty,\qquad
W_n:=\sum_{j\ge n}\sigma_j\downarrow0.
\]

Assume decomposition channels:
\[
D_n=D_\infty+\sum_{j\ge n}\delta_j,\qquad
N_n^X=N_\infty^X+\sum_{j\ge n}\nu_j^X,\quad X\in\{F,\partial\psi,\psi\mathcal D\},
\]
with first-principles shell envelopes
\[
|\delta_j|\le C_D\sigma_j,\qquad
|\nu_j^X|\le C_X\sigma_j.
\]

## Theorem 1 (Shell Bounds -> AN-33 Rate Bounds)

For each \(X\in\{F,\partial\psi,\psi\mathcal D\}\):

1. one-sided tails:
   \[
   |D_n-D_\infty|\le C_DW_n,\qquad
   |N_n^X-N_\infty^X|\le C_XW_n,
   \]
2. pairwise rates:
   \[
   |D_n-D_m|\le C_D(W_n+W_m),\qquad
   |N_n^X-N_m^X|\le C_X(W_n+W_m).
   \]

So AN-33 `(DEN-RATE)`/`(NUM-RATE)` now follow from shell summability and
envelopes.

### Proof sketch

Tail-sum bound for one-sided estimates, then triangle through the common limits.
The pairwise step is exactly the Lean lemma
`abs_sub_le_of_tail_to_limit`.
\(\square\)

## Theorem 2 (First-Principles Normalized Ratio Rate)

Assume additionally denominator floor and one-sided numerator bound:
\[
|D_n|\ge d_0>0,\qquad |N_m^X|\le B_X.
\]
Then for all \(n,m\),
\[
\left|\frac{N_n^X}{D_n}-\frac{N_m^X}{D_m}\right|
\le
\left(\frac{C_X}{d_0}+\frac{B_XC_D}{d_0^2}\right)(W_n+W_m).
\]

### Proof sketch

Use Theorem 1 pairwise bounds and the Lean AN-34L wrapper
`ratio_diff_bound_of_limit_tail_rates` (implemented in
`Claim1lean/WeightedLocalGraphDecay.lean`). \(\square\)

## Corollary (AN-34A Upgrade)

AN-34A removes AN-33 rate postulates by deriving them from shell-tail control:

1. denominator/numerator Cauchy-rate assumptions are no longer primitive,
2. normalized ratio Cauchy rates remain explicit with first-principles constants,
3. AN-33 SD nonlocal weighted-local closure is preserved with this stronger input chain.

## Lean Support (New in AN-34L)

In `research/workspace/proofs/Claim1lean/WeightedLocalGraphDecay.lean`:

1. `abs_sub_le_add_of_dist_to_center`,
2. `abs_sub_le_of_tail_to_limit`,
3. `ratio_diff_bound_of_tail_rates`,
4. `ratio_diff_bound_of_limit_tail_rates`.

These convert shell-limit envelopes directly into ratio-tail bounds.

## Validation Contract

### Assumptions

1. shell decomposition of channels is explicit,
2. shell envelope constants \(C_D,C_X\) are finite and summability-weighted,
3. denominator floor remains explicit in the working parameter window.

### Units and dimensions check

1. \(\sigma_j, W_n\) are dimensionless bookkeeping weights,
2. ratio-rate constants are dimensionless.

### Symmetry/conservation checks

1. shell decomposition does not alter AN-33 symmetry assumptions,
2. no new regulator is introduced.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an34_firstprinciples_tail_rate_check.py
```

The script checks:

1. one-sided shell-tail bounds for denominator and numerators,
2. induced pairwise rate bounds,
3. normalized ratio bound with first-principles constants,
4. SD residual stabilization along exhaustion levels.

### Confidence statement

AN-34A is theorem-grade in this scoped branch under explicit shell decomposition
and denominator-floor assumptions. It strengthens AN-33 by deriving rate bounds
instead of postulating them. Full global reconstruction remains open.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic seed printed by script,
3. Lean build commands:
   - `cd research/workspace/proofs`,
   - `/Users/arivero/.elan/bin/lake build Claim1lean.WeightedLocalGraphDecay`,
   - `/Users/arivero/.elan/bin/lake build Claim1lean`,
4. date anchor: 2026-02-10 (US).

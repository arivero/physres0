# Claim 1 Phase CD (AN-33L-C): Lean Commuting-Limit Wrapper (Exhaustion + De-Regularization)

Date: 2026-02-10 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-10-claim1-d3-an33l-b-projective-dereg-transfer-lean.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-an31-exhaustion-summability-lift.md`
- `research/workspace/proofs/Claim1lean/WeightedLocalGraphDecay.lean`

## Goal

Close AN-33L-C by packaging a machine-checked commuting-limit wrapper that
matches the AN-31/AN-34 interface:

1. exhaustion/projective limits (index \(n\to\infty\)),
2. de-regularization/regularization removal (index \(\eta\to0^+\), modeled as an external limit).

The wrapper is formulated abstractly as a 2-parameter convergence lemma with
explicit quantitative envelopes.

## Target/Model/Existence Declaration (Non-Drift Rule)

1. target dimension: \(d=3\),
2. model class: AN-31/AN-34 scoped oscillatory/de-regularized branch (support lane),
3. existence notion: commuting-limit control for exhaustion vs de-regularization (not a full field reconstruction theorem),
4. geometric \(1/2\)-density role: interpretation only.

## Lean Statement (Machine-Checked)

In `Claim1lean/WeightedLocalGraphDecay.lean`:

`commuting_limit_of_exhaustion_and_regularization_envelopes` proves:

Given sequences

- `u k n` (two-parameter observable/state value; \(k\) = regularization index, \(n\) = exhaustion index),
- `Lk k` (exhaustion-limit proxy per \(k\)),
- `t n` (exhaustion tail envelope with `t n → 0`),
- `e k` (regularization tail envelope with `e k → 0`),

and nonnegative constants \(A,B\), assume:

1. **Exhaustion tail-to-limit envelope**:
   \[
   |u_{k,n}-L_k|\le A\,t_n,
   \]
2. **Regularization Cauchy envelope for the limit proxies**:
   \[
   |L_k-L_{k'}|\le B\,(e_k+e_{k'}),
   \]
3. `t n → 0`, `e k → 0`, with nonnegativity of \(t,e,A,B\).

Then there exists \(L\) such that:

1. \(L_k\to L\) as \(k\to\infty\),
2. \(u_{k,n}\to L\) as \((k,n)\to\infty\) jointly (product `atTop`),

which is the exact abstract commuting-limit wrapper needed for AN-31/AN-34:
exhaustion control plus regularization-removal control implies a unique joint
limit in the scoped branch.

## How It Uses AN-33L-A/B

AN-33L-A supplies exhaustion-indexed pairwise bounds (tail-to-limit ⇒ pairwise),
and AN-33L-B supplies mismatch-penalty transfer across regularizations.
AN-33L-C then packages the final step: a single lemma that turns explicit tail
envelopes into joint convergence.

## Validation Contract

### Assumptions

1. explicit exhaustion tail envelope `t n`,
2. explicit regularization envelope `e k`,
3. nonnegativity of tail envelopes and constants.

### Units and dimensions check

1. `t n`, `e k` are dimensionless bookkeeping terms,
2. convergence constants are dimensionless.

### Symmetry/conservation checks

No symmetry assumptions are modified; this is a pure analytic/index lemma.

### Independent cross-check path

Run:

```bash
cd research/workspace/proofs
/Users/arivero/.elan/bin/lake build Claim1lean.WeightedLocalGraphDecay
```

### Confidence statement

AN-33L-C is machine-checked and closes the commuting-limit wrapper at the
support-lane level. Remaining work is field-side: exhibit the concrete `t n`
and `e k` envelopes in the target weighted-local nonlocal channels and feed
this wrapper into the AN-31/AN-34 theorem statements.

### Reproducibility metadata

1. Lean toolchain: `/Users/arivero/.elan/bin/lean`, `/Users/arivero/.elan/bin/lake`,
2. build command listed above,
3. date anchor: 2026-02-10 (US).

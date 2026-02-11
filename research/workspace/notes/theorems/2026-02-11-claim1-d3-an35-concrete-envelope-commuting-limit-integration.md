# Claim 1 Phase CE (AN-35): Concrete `t n` / `e k` Envelopes and Commuting-Limit Integration

Date: 2026-02-11 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-an31-exhaustion-summability-lift.md`
- `research/workspace/notes/theorems/2026-02-10-claim1-d3-an34-firstprinciples-tail-rate-transmutation.md`
- `research/workspace/notes/theorems/2026-02-10-claim1-d3-an33l-c-commuting-limit-wrapper-lean.md`
- `research/workspace/proofs/Claim1lean/WeightedLocalGraphDecay.lean`

## Goal

Close the AN-roadmap "next" item by exhibiting explicit exhaustion and
regularization envelopes for the weighted-local graph-decay nonlocal channel,
then wiring them directly into the Lean commuting-limit wrapper.

## Target/Model/Existence Declaration (Non-Drift Rule)

1. target dimension: \(d=3\),
2. model class: AN-24/AN-34 scoped oscillatory/de-regularized nearest-neighbor lattice \(\phi^4\) branch,
3. existence notion: exhaustion+regularization joint limit for weighted-local nonlocal observables (support-lane closure, not full reconstruction),
4. geometric \(1/2\)-density role: interpretation only.

## Concrete Envelope Choice

Let \(H_n\uparrow H_\infty\) be the AN-31 exhaustion and define the AN-31 tail weight:
\[
t_n := W_n^{\mathrm{tail}}
= \sum_{v\in V(H_\infty)\setminus V(H_n)} w(v).
\]

For regularization index \(k\), choose
\[
\eta_k = \eta_0\,2^{-k},\qquad
e_k := \eta_k^{\alpha} + \lambda^k,
\]
with constants \(\eta_0>0\), \(\alpha>0\), \(0<\lambda<1\).

Interpretation:

1. \(\eta_k^\alpha\): de-regularization mismatch scale from AN-33L-B transfer bounds,
2. \(\lambda^k\): additional channel/proxy mismatch decay (projective/transfer bookkeeping remainder).

Both are explicit and summable-tail compatible.

Diagnostic instance used in the independent numerical check:
\[
\eta_0=0.32,\qquad \alpha=0.75,\qquad \lambda=0.57.
\]

## Envelope-to-Wrapper Assumption Map

Use Lean theorem
`commuting_limit_of_exhaustion_and_regularization_envelopes`
with:

1. \(u_{k,n} := \omega_{\eta_k,\infty,H_n}^{(\kappa)}(F)\),
2. \(L_k := \omega_{\eta_k,\infty,H_\infty}^{(\kappa)}(F)\),
3. \(t_n := W_n^{\mathrm{tail}}\),
4. \(e_k := \eta_k^\alpha + \lambda^k\).

Required envelopes:
\[
|u_{k,n}-L_k|\le A\,t_n,\qquad
|L_k-L_{k'}|\le B\,(e_k+e_{k'}).
\]

The first is the AN-31/AN-34 exhaustion envelope; the second is the
regularization Cauchy envelope from AN-33L-B transfer penalties plus
de-regularization decay.

## Theorem 1 (Explicit Envelope Decay)

Under AN-31 summability (\(W_n^{\mathrm{tail}}\to0\)) and the geometric schedule
above:
\[
t_n \to 0,\qquad e_k\to0,\qquad t_n,e_k\ge0.
\]

### Proof

1. \(t_n=W_n^{\mathrm{tail}}\to0\) is AN-31 summable-tail hypothesis.
2. \(\eta_k^\alpha\to0\) because \(\eta_k=\eta_0 2^{-k}\to0\).
3. \(\lambda^k\to0\) for \(0<\lambda<1\).
4. Sum of two vanishing nonnegative terms vanishes, so \(e_k\to0\). \(\square\)

## Theorem 2 (Concrete Joint-Limit Closure)

Assume the envelope inequalities above with the concrete \(t_n,e_k\).  
Then there exists \(L\) such that:

1. \(L_k\to L\) as \(k\to\infty\),
2. \(u_{k,n}\to L\) jointly as \((k,n)\to\infty\),

equivalently, exhaustion and de-regularization commute on this observable
channel in the scoped branch.

### Proof

Apply
`commuting_limit_of_exhaustion_and_regularization_envelopes`
with the mapping above and Theorem 1 decay facts. \(\square\)

## Corollary (AN-35 Upgrade)

The "existential envelope" step in the AN-31/AN-34 interface is now concrete:

1. exhaustion envelope fixed as \(t_n=W_n^{\mathrm{tail}}\),
2. regularization envelope fixed as \(e_k=\eta_k^\alpha+\lambda^k\),
3. Lean commuting-limit wrapper is directly consumable by field-side notes with no
   placeholder envelope symbols.

## Validation Contract

### Assumptions

1. AN-31 summable-tail exhaustion setup,
2. AN-33L-B transfer mismatch bounds in a regularization schedule \(\eta_k\),
3. explicit constants \(\eta_0,\alpha,\lambda,A,B\) in the working channel.

### Units and dimensions check

1. \(t_n\), \(e_k\), \(W_n^{\mathrm{tail}}\), \(\eta_k^\alpha\), \(\lambda^k\) are dimensionless bookkeeping quantities,
2. ratio/transfer constants \(A,B\) are dimensionless.

### Symmetry/conservation checks

1. no change to AN-31 graph/exhaustion symmetry assumptions,
2. no additional symmetry breaking introduced by regularization schedule choice.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an35_concrete_envelope_commuting_limit_check.py
```

The script verifies:

1. \(t_n\to0\), \(e_k\to0\) numerically for explicit schedules,
2. envelope inequalities in a synthetic channel (`|u_{k,n}-L_k| <= A t_n`, `|L_k-L_{k'}| <= B(e_k+e_{k'})`),
3. monotone decrease of joint-limit residuals.

Observed run snapshot (seed `2026021101`):

1. `t_last=3.31026663e-05`,
2. `e_last=8.84898359e-06`,
3. `sup_tail_last=4.23440497e-05`,
4. `all_checks_pass=True`.

### Confidence statement

AN-35 is theorem-grade in the scoped support lane: envelope placeholders are now
concretized and mapped to the machine-checked commuting-limit lemma.
Full global interacting reconstruction remains open.

### Reproducibility metadata

1. Python command above with deterministic seed in script output,
2. Lean anchor theorem (already integrated from prior lane): `research/workspace/proofs/Claim1lean/WeightedLocalGraphDecay.lean`,
3. CPU-bound execution note: no new Lean builds were launched in this AN-35 cycle,
4. date anchor: 2026-02-11 (US).

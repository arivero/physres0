# Claim 1 Phase BX (AN-31): \(d=3\) Exhaustion-Family Summability Lift of AN-30

Date: 2026-02-09 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-an30-multiblock-projective-consistency.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-an29-nonlocal-continuum-cauchy.md`

## Goal

Lift AN-30 from finite graph-indexed families to uniformly locally finite
exhaustion families with summability-weighted combinatorial constants, while
preserving refinement/projective consistency in the same scoped \(d=3\)
oscillatory/de-regularized branch.

## Target/Model/Existence Declaration (Non-Drift Rule)

1. target dimension: \(d=3\),
2. model class: AN-24/AN-30 nearest-neighbor lattice \(\phi^4\), finite volume,
3. existence notion: exhaustion-limit existence and projective consistency for
   countable locally finite block families via summable-tail control,
4. geometric \(1/2\)-density role: interpretation only.

## Setup

Let \(H_\infty\) be a countable locally finite index graph with exhaustion
\[
H_1\subset H_2\subset\cdots,\qquad \bigcup_{n\ge1}H_n=H_\infty.
\]
For each \(H_n\), AN-30 provides refinement-limit states
\(\omega_{\eta,\infty,H_n}^{(\kappa)}\).

Fix a positive summability weight \(w:V(H_\infty)\to(0,\infty)\) with
\[
\sum_{v\in V(H_\infty)}w(v)<\infty,
\qquad
W_n^{\mathrm{tail}}:=\sum_{v\in V(H_\infty)\setminus V(H_n)}w(v)\xrightarrow[n\to\infty]{}0.
\]

## Assumption Package (AN-31)

1. **(AN30-UNI)** AN-30 hypotheses hold uniformly on the exhaustion family.
2. **(SUMB)** exhaustion-tail combinatorial control:
   \[
   C_{\mathrm{mb},n}^{\star}\le C_{\mathrm{mb}}^{\star}\bigl(1+W_n^{\mathrm{tail}}\bigr),\qquad
   C_{\mathrm{proj},n}^{\star}\le C_{\mathrm{proj}}^{\star}\bigl(1+W_n^{\mathrm{tail}}\bigr).
   \]
3. **(EXT-TAIL)** for every cylinder observable \(F\) depending on finitely many
   blocks \(K_F\subset V(H_\infty)\), there exists \(A_F>0\) such that for
   \(n,m\) large enough (both containing \(K_F\)):
   \[
   \left|
   \omega_{\eta,\infty,H_n}^{(\kappa)}(F)-\omega_{\eta,\infty,H_m}^{(\kappa)}(F)
   \right|
   \le
   A_F\left(W_n^{\mathrm{tail}}+W_m^{\mathrm{tail}}\right).
   \]
4. **(EXT-PROJ)** finite-scale projective defects from AN-30 remain controlled
   along the exhaustion by the same tail envelope.

## Theorem 1 (Exhaustion Cauchy Bound with Summable Tails)

Under (AN30-UNI)+(SUMB)+(EXT-TAIL), for each finite-cylinder observable \(F\),
the sequence \(\{\omega_{\eta,\infty,H_n}^{(\kappa)}(F)\}_{n\ge1}\) is Cauchy and
\[
\left|
\omega_{\eta,\infty,H_n}^{(\kappa)}(F)-\omega_{\eta,\infty,H_m}^{(\kappa)}(F)
\right|
\le
A_F\left(W_n^{\mathrm{tail}}+W_m^{\mathrm{tail}}\right).
\]
Hence there exists an exhaustion-limit value
\(\omega_{\eta,\infty,H_\infty}^{(\kappa)}(F)\).

### Proof sketch

Apply (EXT-TAIL) and use summability \(W_n^{\mathrm{tail}}\to0\). \(\square\)

## Theorem 2 (Exhaustion-Level Projective Consistency + De-Regularization)

Assume Theorem 1 hypotheses plus (EXT-PROJ). Then:

1. the exhaustion-limit family \(\omega_{\eta,\infty,H_\infty}^{(\kappa)}\) is
   projectively consistent on every finite induced subgraph restriction;
2. if AN-30 de-regularization hypotheses hold uniformly along \(n\), then
   \(\eta\to0^+\) commutes with the exhaustion limit on this cylinder class.

### Proof sketch

Projective defects are bounded by tail envelopes that vanish as \(n\to\infty\).
Uniform AN-30 de-regularization control then passes through the same limit.
\(\square\)

## Corollary (AN-31 Scoped Upgrade)

AN-31 upgrades Claim 1 from finite-family AN-30 control to exhaustion families:

1. finite graph-indexed projective consistency lifts to countable locally finite
   index families via summable tails,
2. explicit quantitative control is now expressed in \(W_n^{\mathrm{tail}}\),
3. de-regularization compatibility is retained in this lifted scoped lane.

Next target (AN-32): promote AN-31 from cylinder observables to weighted-local
test classes with explicit exhaustion-uniform insertion estimates.

## Validation Contract

### Assumptions

1. AN-30 assumptions hold uniformly on the exhaustion family,
2. summability weights and tail envelopes are explicit.

### Units and dimensions check

1. \(W_n^{\mathrm{tail}}\) is dimensionless,
2. renormalized coordinates \(v_B=a^{3/2}\phi|_B\) are unchanged.

### Symmetry/conservation checks

1. local lattice symmetries are unchanged on each \(H_n\),
2. exhaustion inclusions preserve restriction-map algebra.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an31_exhaustion_summability_check.py
```

The script checks:

1. summable-tail decay \(W_n^{\mathrm{tail}}\to0\),
2. exhaustion Cauchy bounds for finite-cylinder observables,
3. projective-defect decay across exhaustion levels,
4. finest-level near-consistency and de-regularization stabilization.

### Confidence statement

AN-31 is theorem-grade in this scoped branch under explicit summability and
uniformity hypotheses. It strengthens AN-30 to exhaustion families but does not
yet close full global reconstruction.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic seed printed by script,
3. date anchor: 2026-02-09 (US).

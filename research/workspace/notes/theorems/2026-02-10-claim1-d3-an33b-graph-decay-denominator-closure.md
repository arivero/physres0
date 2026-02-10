# Claim 1 Phase BZ (AN-33B): \(d=3\) Graph-Decay Nonlocal Weighted-Local Closure

Date: 2026-02-10 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-10-claim1-d3-an33-graph-decay-nonlocal-weighted-local.md`
- `research/workspace/notes/theorems/2026-02-10-claim1-d3-an32-weighted-local-sdtest-lift.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-an31-exhaustion-summability-lift.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-an30-multiblock-projective-consistency.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-an29-nonlocal-continuum-cauchy.md`
- `research/workspace/notes/theorems/2026-02-10-claim1-lean-weighted-local-graph-decay-bridge.md`

## Goal

Close AN-33 from the AN-33A skeleton by proving, in the same scoped \(d=3\)
branch, that:

1. graph-decay nonlocal weighted-local channels inherit AN-32 envelope/tail control,
2. denominator-rate bookkeeping is explicit at normalized-state level,
3. SD pass-through extends to this nonlocal weighted-local class.

## Target/Model/Existence Declaration (Non-Drift Rule)

1. target dimension: \(d=3\),
2. model class: AN-24/AN-32 nearest-neighbor lattice \(\phi^4\), scoped oscillatory/de-regularized branch,
3. existence notion: exhaustion-limit existence + SD pass-through + denominator-rate normalized Cauchy control for graph-decay weighted-nonlocal channels,
4. geometric \(1/2\)-density role: interpretation only.

## Setup

Keep AN-32 exhaustion family \(H_n\uparrow H_\infty\), summable weights
\(w(v)>0\), and tails \(W_n^{\mathrm{tail}}\to0\).

For each vertex \(u\), define graph-decay nonlocal channels:
\[
\widetilde F_u:=\sum_v K^F_{uv}F_v,\qquad
\widetilde\psi_u:=\sum_v K^\psi_{uv}\psi_v,
\]
and weighted-nonlocal classes
\[
F^{\mathrm{nl}}=\sum_u \alpha_u\widetilde F_u,\qquad
\psi^{\mathrm{nl}}=\sum_u \beta_u\widetilde\psi_u.
\]

Introduce cutoff profiles \(\chi_r\in[0,1]\) and nonlocal truncations
\(F^{\mathrm{nl},(r)}\), \(\psi^{\mathrm{nl},(r)}\) by replacing coefficients with
\(\chi_r\alpha,\chi_r\beta\).

## Assumption Package (AN-33B)

1. **(AN32-UNI)** AN-32 assumptions and conclusions hold for local weighted classes.
2. **(GD-F/GD-\(\psi\))** graph-decay column envelopes:
   \[
   \sum_u |\alpha_u|\,|K^F_{uv}| \le C_F^{\mathrm{gd}}\,w(v),\qquad
   \sum_u |\beta_u|\,|K^\psi_{uv}| \le C_\psi^{\mathrm{gd}}\,w(v).
   \]
3. **(LOC-UNI)** local channels satisfy AN-32 weighted envelopes (`OBS-UNI`,
   `DER-UNI`, `INS-UNI`).
4. **(DEN-FLOOR)** exhaustion denominators satisfy
   \[
   |D_n(\eta,\kappa)|\ge d_0>0.
   \]
5. **(DEN-RATE)** denominator exhaustion rate:
   \[
   |D_n-D_m|\le A_D\,(W_n^{\mathrm{tail}}+W_m^{\mathrm{tail}}).
   \]
6. **(NUM-RATE)** numerator exhaustion rates for nonlocal channels:
   \[
   |N_n^X-N_m^X|\le A_X\,(W_n^{\mathrm{tail}}+W_m^{\mathrm{tail}}),\quad
   X\in\{F,\partial\psi,\psi\mathcal D\}.
   \]
7. **(NUM-BOUND)** one-sided numerator bounds:
   \[
   |N_m^X|\le B_X,\quad X\in\{F,\partial\psi,\psi\mathcal D\}.
   \]

## Theorem 1 (Graph-Decay Lift of Weighted-Local Envelopes)

Under (GD-F/GD-\(\psi\))+(LOC-UNI):

1. nonlocal weighted envelopes are controlled by local weighted envelopes with
   constants multiplied by \(C_F^{\mathrm{gd}},C_\psi^{\mathrm{gd}}\),
2. nonlocal truncation tails obey
   \[
   \mathrm{Tail}_{\chi_r}(x)\le
   M\sum_v (1-\chi_r(v))\,w(v)\xrightarrow[r\to\infty]{}0.
   \]

### Proof sketch

Apply AN-32L Lean lemmas:

1. `weightedL1_image_le_of_column_decay` for graph-decay channel lifting,
2. `weightedTailL1_le_of_uniform_bound` for truncation tails.
\(\square\)

## Theorem 2 (Explicit Denominator-Rate Normalized Cauchy Bound)

Let \(R_n^X:=N_n^X/D_n\). Under (DEN-FLOOR)+(DEN-RATE)+(NUM-RATE)+(NUM-BOUND):
\[
|R_n^X-R_m^X|
\le
\left(\frac{A_X}{d_0}+\frac{B_XA_D}{d_0^2}\right)
(W_n^{\mathrm{tail}}+W_m^{\mathrm{tail}}),
\quad
X\in\{F,\partial\psi,\psi\mathcal D\}.
\]
Hence each normalized channel is exhaustion-Cauchy with explicit tail rate.

### Proof sketch

Use AN-32L denominator bookkeeping chain:

1. `abs_inv_sub_inv_le_of_abs_sub_le`,
2. `ratio_diff_bound_of_denominator_rates`.

Substitute \(\varepsilon_N=A_X(W_n^{\mathrm{tail}}+W_m^{\mathrm{tail}})\),
\(\varepsilon_D=A_D(W_n^{\mathrm{tail}}+W_m^{\mathrm{tail}})\). \(\square\)

## Theorem 3 (AN-33B Nonlocal Weighted SD Pass-Through)

Assume Theorems 1-2 hypotheses and finite-level SD closure for truncations
\((F^{\mathrm{nl},(r)},\psi^{\mathrm{nl},(r)})\). Then
\[
\omega_{\eta,\infty,H_\infty}^{(\kappa)}(\partial\psi^{\mathrm{nl}})
=
c_\eta\,
\omega_{\eta,\infty,H_\infty}^{(\kappa)}(\psi^{\mathrm{nl}}\mathcal D).
\]

### Proof sketch

1. pass \(r\to\infty\) using Theorem 1 truncation-tail estimates,
2. pass \(n\to\infty\) using Theorem 2 normalized Cauchy rates on both SD sides,
3. keep AN-32 de-regularized branch structure unchanged. \(\square\)

## Corollary (AN-33 Scoped Upgrade)

AN-33 is closed in this scoped branch:

1. AN-32 weighted-local classes now include graph-decay nonlocal weighted-local channels,
2. normalized-state denominator bookkeeping is explicit and quantitative,
3. SD pass-through persists for the nonlocal weighted class in exhaustion limit.

## Lean Dependency Map (Used in Closure)

1. `weightedL1_image_le_of_column_decay` -> Theorem 1 channel lift,
2. `weightedTailL1_le_of_uniform_bound` -> Theorem 1 tail limit,
3. `abs_inv_sub_inv_le_of_abs_sub_le` -> Theorem 2 reciprocal denominator rate,
4. `ratio_diff_bound_of_denominator_rates` -> Theorem 2 normalized ratio rate.

## Validation Contract

### Assumptions

1. AN-32 local weighted lane remains valid,
2. graph-decay and denominator-rate hypotheses are explicit,
3. closure is scoped to this branch (not global interacting reconstruction).

### Units and dimensions check

1. \(W_n^{\mathrm{tail}}\), weighted norms, and ratio-rate constants are dimensionless,
2. renormalized block coordinates and local insertion channels are unchanged from AN-32.

### Symmetry/conservation checks

1. no new symmetry-breaking regulator is introduced,
2. exhaustion/projective maps are unchanged; only observable/test class is widened.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an33_graph_decay_nonlocal_weighted_local_check.py
```

The script checks:

1. graph-decay column envelope inequalities,
2. truncation-tail bounds,
3. denominator-rate normalized Cauchy inequalities,
4. nonlocal SD residual stabilization along exhaustion levels.

### Confidence statement

AN-33 is theorem-grade in this scoped branch under explicit graph-decay and
denominator-rate assumptions inherited from the AN-29/AN-30/AN-31/AN-32 lane.
Full global interacting continuum reconstruction remains open.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic seed printed by script,
3. date anchor: 2026-02-10 (US),
4. Lean support build:
   - `cd research/workspace/proofs`,
   - `/Users/arivero/.elan/bin/lake build Claim1lean.WeightedLocalGraphDecay`.

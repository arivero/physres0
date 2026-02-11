# Claim 1 Phase CE (AN-37): Field-Tail-Calibrated \(\varepsilon\)-Schedule

Date: 2026-02-11 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-an31-exhaustion-summability-lift.md`
- `research/workspace/notes/theorems/2026-02-11-claim1-d3-an36-explicit-epsilon-schedule-from-envelopes.md`

## Goal

Replace AN-36's geometric proxy tail majorant with a branch-native exhaustion-tail
schedule built directly from AN-31 data:
\[
t_n := W_n^{\mathrm{tail}}.
\]

## Setup

Assume the AN-35/AN-36 bound:
\[
|u_{k,n}-L|\le A\,t_n + B\,e_k,\qquad A,B>0,
\]
with concrete regularization envelope
\[
e_k=\eta_0^\alpha 2^{-\alpha k}+\lambda^k,\qquad
\eta_0>0,\ \alpha>0,\ 0<\lambda<1.
\]

From AN-31, \(t_n=W_n^{\mathrm{tail}}\) is nonnegative and decreasing to zero.

Define
\[
q:=\max(2^{-\alpha},\lambda),\qquad C_e:=\eta_0^\alpha+1,\qquad e_k\le C_e q^k.
\]

## Theorem 1 (Field-Calibrated Index Budget)

For \(\varepsilon>0\), define
\[
n_\varepsilon^{\mathrm{field}}
:=
\min\left\{n:\ A\,W_n^{\mathrm{tail}}\le\frac{\varepsilon}{2}\right\},
\]
\[
k_\varepsilon
:=
\left\lceil
\frac{\log\!\left(\frac{2BC_e}{\varepsilon}\right)}{|\log q|}
\right\rceil.
\]
Then for all \(n\ge n_\varepsilon^{\mathrm{field}}\), \(k\ge k_\varepsilon\):
\[
|u_{k,n}-L|\le\varepsilon.
\]

### Proof

By definition of \(n_\varepsilon^{\mathrm{field}}\) and monotonicity of
\(W_n^{\mathrm{tail}}\):
\[
A\,W_n^{\mathrm{tail}}\le\frac{\varepsilon}{2}\quad(n\ge n_\varepsilon^{\mathrm{field}}).
\]
By AN-36 regularization bound:
\[
B\,e_k\le\frac{\varepsilon}{2}\quad(k\ge k_\varepsilon).
\]
Sum the two contributions. \(\square\)

## Corollary (Proxy-Free Exhaustion Calibration)

AN-37 removes the remaining proxy step in AN-36:

1. no surrogate \(t_n\le C_t\rho^n\) is required,
2. tolerance-to-index mapping uses the field-native tail profile
   \(W_n^{\mathrm{tail}}\) directly,
3. \(\varepsilon\)-schedules can be recomputed immediately when AN-31 tail data
   is updated.

## Corollary (Crossover Diagnostic vs Geometric Proxy)

Comparing AN-37 field schedules with AN-36 geometric-proxy schedules yields a
two-regime behavior:

1. moderate-precision regime: field-calibrated \(n_\varepsilon\) can be smaller,
2. strict-precision regime: field-calibrated \(n_\varepsilon\) can be larger when
   AN-31 tails carry slower-decay components.

Hence AN-37 is not only a calibration refinement; it is a safety upgrade against
proxy-induced underestimation in high-precision targets.

## Scoped Numeric Instantiation

Using the AN-31 deterministic tail family from
`claim1_d3_an31_exhaustion_summability_check.py`, AN-35 constants
\((A,B,\eta_0,\alpha,\lambda)\), and AN-36 \(k_\varepsilon\)-formula:

1. field schedules \(n_\varepsilon^{\mathrm{field}}\) are monotone in
   \(\varepsilon\),
2. bound checks pass on sampled tail blocks
   \(n\ge n_\varepsilon^{\mathrm{field}},k\ge k_\varepsilon\),
3. both comparison regimes are observed on the tested \(\varepsilon\)-grid
   (`n_field < n_geo` for moderate \(\varepsilon\), `n_field > n_geo` for strict
   \(\varepsilon\)).

## Validation Contract

### Assumptions

1. AN-31 tail profile \(W_n^{\mathrm{tail}}\) is explicit and monotone,
2. AN-35 envelope inequality \(|u_{k,n}-L|\le A W_n^{\mathrm{tail}} + B e_k\),
3. regularization schedule parameters are fixed.

### Units and dimensions check

1. \(W_n^{\mathrm{tail}}, e_k, \varepsilon\) are dimensionless,
2. \(A,B,C_e\) are dimensionless.

### Symmetry/conservation checks

1. no new symmetry assumptions are introduced,
2. exhaustion-index monotonicity follows from AN-31 summability structure.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an37_field_tail_schedule_check.py
```

The script verifies:

1. monotonicity and decay of \(W_n^{\mathrm{tail}}\),
2. correctness of \(n_\varepsilon^{\mathrm{field}},k_\varepsilon\) on a tolerance grid,
3. sampled-tail block bound satisfaction
   `A*W_n_tail + B*e_k <= epsilon`,
4. comparison with AN-36 geometric-proxy \(n_\varepsilon\).

### Confidence statement

AN-37 upgrades AN-36 by calibrating exhaustion budgets directly from field-lane
AN-31 data. The result remains scoped to the existing weighted-local branch.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic parameter/tolerance grid in script output,
3. date anchor: 2026-02-11 (US).

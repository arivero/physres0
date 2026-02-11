# Claim 1 Phase CE (AN-38): Hybrid Robust \(\varepsilon\)-Schedule with Safety Certificate

Date: 2026-02-11 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-11-claim1-d3-an36-explicit-epsilon-schedule-from-envelopes.md`
- `research/workspace/notes/theorems/2026-02-11-claim1-d3-an37-field-tail-calibrated-epsilon-schedule.md`

## Goal

Unify AN-36 and AN-37 into one robust tolerance-to-index schedule that:

1. preserves analytic proxy efficiency when valid,
2. inherits AN-37 field-tail safety in strict-tolerance regimes,
3. certifies no underestimation of required exhaustion indices.

## Setup

As in AN-35/AN-36/AN-37, assume
\[
|u_{k,n}-L|\le A\,t_n + B\,e_k,\qquad A,B>0,
\]
with
\[
e_k=\eta_0^\alpha 2^{-\alpha k}+\lambda^k,\qquad
q:=\max(2^{-\alpha},\lambda),\qquad C_e:=\eta_0^\alpha+1.
\]

Define schedules:

1. AN-36 proxy exhaustion schedule
   \[
   n_\varepsilon^{\mathrm{proxy}}
   :=
   \left\lceil
   \frac{\log\!\left(\frac{2AC_t}{\varepsilon}\right)}{|\log\rho|}
   \right\rceil,
   \]
2. AN-37 field schedule
   \[
   n_\varepsilon^{\mathrm{field}}
   :=
   \min\left\{n:\ A\,W_n^{\mathrm{tail}}\le\frac{\varepsilon}{2}\right\},
   \]
3. regularization schedule (unchanged)
   \[
   k_\varepsilon
   :=
   \left\lceil
   \frac{\log\!\left(\frac{2BC_e}{\varepsilon}\right)}{|\log q|}
   \right\rceil.
   \]

Define hybrid exhaustion schedule:
\[
n_\varepsilon^{\mathrm{hyb}}
:=
\max\!\big(n_\varepsilon^{\mathrm{proxy}},\,n_\varepsilon^{\mathrm{field}}\big).
\]

## Theorem 1 (Hybrid Robust \(\varepsilon\)-Bound)

For every \(\varepsilon>0\), if \(n\ge n_\varepsilon^{\mathrm{hyb}}\) and
\(k\ge k_\varepsilon\), then
\[
|u_{k,n}-L|\le\varepsilon.
\]

### Proof

Because \(n_\varepsilon^{\mathrm{hyb}}\ge n_\varepsilon^{\mathrm{field}}\), AN-37
implies
\[
A\,W_n^{\mathrm{tail}}\le\frac{\varepsilon}{2}.
\]
Because \(k\ge k_\varepsilon\), AN-36 regularization control implies
\[
B\,e_k\le\frac{\varepsilon}{2}.
\]
Therefore
\[
|u_{k,n}-L|\le A\,W_n^{\mathrm{tail}}+B\,e_k\le\varepsilon.
\]
\(\square\)

## Theorem 2 (Underestimation-Safety Certificate)

For every \(\varepsilon>0\):
\[
n_\varepsilon^{\mathrm{hyb}}\ge n_\varepsilon^{\mathrm{proxy}},\qquad
n_\varepsilon^{\mathrm{hyb}}\ge n_\varepsilon^{\mathrm{field}}.
\]
Hence hybrid schedules cannot underestimate either constituent requirement.

### Proof

Immediate from definition as pointwise maximum. \(\square\)

## Corollary (Automatic Regime Switching)

Hybrid scheduling implements an explicit switch:

1. proxy-dominated region:
   \(n_\varepsilon^{\mathrm{proxy}}\ge n_\varepsilon^{\mathrm{field}}\),
2. field-dominated region:
   \(n_\varepsilon^{\mathrm{field}}>n_\varepsilon^{\mathrm{proxy}}\).

So AN-38 keeps moderate-\(\varepsilon\) efficiency while preventing strict-\(\varepsilon\)
underestimation exposed in AN-37 crossover diagnostics.

## Scoped Numeric Instantiation

Using AN-35 constants and AN-31 deterministic tails:

1. \(n_\varepsilon^{\mathrm{hyb}}\), \(k_\varepsilon\) are monotone in
   \(\varepsilon\downarrow0\),
2. tail-block bounds pass for sampled
   \(n\ge n_\varepsilon^{\mathrm{hyb}},k\ge k_\varepsilon\),
3. both switch regimes are observed on the tested \(\varepsilon\)-grid.

## Validation Contract

### Assumptions

1. AN-31 tail profile \(W_n^{\mathrm{tail}}\) explicit and monotone,
2. AN-35 envelope inequality with constants \(A,B\),
3. AN-36/AN-37 schedule definitions are available.

### Units and dimensions check

1. \(W_n^{\mathrm{tail}}, e_k, \varepsilon\) are dimensionless,
2. schedule indices \(n_\varepsilon^{\mathrm{proxy}}, n_\varepsilon^{\mathrm{field}}, n_\varepsilon^{\mathrm{hyb}}, k_\varepsilon\) are integers.

### Symmetry/conservation checks

1. no new dynamics/symmetry assumptions beyond AN-35/AN-37,
2. hybrid rule is purely quantitative post-processing of validated envelopes.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an38_hybrid_schedule_check.py
```

The script verifies:

1. monotonicity of proxy/field/hybrid schedules,
2. underestimation-safety inequalities (hybrid dominates both constituents),
3. sampled-tail bound satisfaction
   `A*W_n_tail + B*e_k <= epsilon`,
4. presence of both switch regimes on the deterministic tolerance grid.

### Confidence statement

AN-38 closes the schedule-robustness gap by combining AN-36 analytic speed with
AN-37 strict-tolerance safety in one certified rule. Global interacting closure
remains open.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic tolerance grid and constants printed by script,
3. date anchor: 2026-02-11 (US).

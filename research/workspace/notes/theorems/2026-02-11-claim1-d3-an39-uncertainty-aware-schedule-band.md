# Claim 1 Phase CF (AN-39): Uncertainty-Aware Hybrid Schedule Band

Date: 2026-02-11 (US)
Depends on:
- `research/workspace/notes/theorems/2026-02-11-claim1-d3-an38-hybrid-robust-epsilon-schedule.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-an31-exhaustion-summability-lift.md`

## Goal

Upgrade AN-38 from deterministic tails to an uncertainty-certified schedule rule that remains safe when field-tail estimates are noisy or biased.

## Setup

Assume the AN-35 envelope:
\[
|u_{k,n}-L| \le A\,W_n^{\mathrm{tail}} + B\,e_k,
\qquad
A,B>0,
\]
with regularization channel
\[
e_k = \eta_0^\alpha 2^{-\alpha k} + \lambda^k,
\quad
q:=\max(2^{-\alpha},\lambda),
\quad
C_e:=\eta_0^\alpha+1.
\]

Suppose we only have estimated tails \(\widehat W_n\) with deterministic uncertainty radii
\(\delta_n\ge0\) satisfying
\[
W_n^{\mathrm{tail}} \le \widehat W_n + \delta_n
\quad\text{for all }n.
\]

Define robust field schedule
\[
n_\varepsilon^{\mathrm{band}}
:=
\min\left\{n:\ A(\widehat W_n+\delta_n)\le\frac{\varepsilon}{2}\right\},
\]
and keep the AN-36 regularization schedule
\[
k_\varepsilon
:=
\left\lceil
\frac{\log\!\left(\frac{2BC_e}{\varepsilon}\right)}{|\log q|}
\right\rceil.
\]

For compatibility with AN-38, define hybrid-safe exhaustion index
\[
n_\varepsilon^{\mathrm{hyb-band}}
:=
\max\!\left(n_\varepsilon^{\mathrm{hyb}},\ n_\varepsilon^{\mathrm{band}}\right).
\]

## Theorem 1 (Band-Safe Epsilon Control)

For every \(\varepsilon>0\), if \(n\ge n_\varepsilon^{\mathrm{hyb-band}}\) and
\(k\ge k_\varepsilon\), then
\[
|u_{k,n}-L|\le\varepsilon.
\]

### Proof

From \(n\ge n_\varepsilon^{\mathrm{band}}\):
\[
A(\widehat W_n+\delta_n)\le\frac{\varepsilon}{2}.
\]
Using \(W_n^{\mathrm{tail}}\le \widehat W_n+\delta_n\),
\[
A W_n^{\mathrm{tail}}\le\frac{\varepsilon}{2}.
\]
From \(k\ge k_\varepsilon\), AN-36 gives \(B e_k\le\varepsilon/2\). Therefore
\[
|u_{k,n}-L|\le A W_n^{\mathrm{tail}}+B e_k\le\varepsilon.
\]
\(\square\)

## Theorem 2 (Anti-Underestimation Guarantee)

If a naive schedule
\[
n_\varepsilon^{\mathrm{naive}}:=\min\{n:A\widehat W_n\le\varepsilon/2\}
\]
ignores \(\delta_n\), then
\[
n_\varepsilon^{\mathrm{band}}\ge n_\varepsilon^{\mathrm{naive}}
\]
whenever \(\delta_n\not\equiv0\). Thus AN-39 explicitly guards against
underestimated exhaustion indices caused by optimistic tail estimates.

## Corollary (Operational Rule)

In updates where only estimated tails are available, use
\(n_\varepsilon^{\mathrm{hyb-band}}\) instead of AN-38 alone. This preserves
AN-38 efficiency when uncertainty is small while certifying safety under bounded
estimation error.

## Validation Contract

### Assumptions

1. AN-35 envelope constants \((A,B)\) are valid,
2. deterministic uncertainty envelope \(\delta_n\) upper-bounds tail estimation error,
3. AN-36 regularization channel assumptions hold.

### Units and dimensions check

1. \(W_n^{\mathrm{tail}},\widehat W_n,\delta_n,e_k,\varepsilon\) are dimensionless,
2. schedule outputs \(n_\varepsilon^{\mathrm{band}}, n_\varepsilon^{\mathrm{hyb-band}}, k_\varepsilon\) are integers.

### Symmetry/conservation checks

1. AN-39 does not alter dynamics; it only tightens quantitative scheduling,
2. all conservation structures used in AN-35/AN-38 remain unchanged.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an39_uncertainty_schedule_band_check.py
```

The script verifies:

1. `W_true <= W_hat + delta` across deterministic tail blocks,
2. robust schedule bound satisfaction,
3. existence of at least one epsilon where naive schedule fails while robust
   schedule passes.

### Confidence statement

AN-39 closes the schedule-risk gap for data-driven tail updates by adding a
provable uncertainty band to AN-38.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic tail/estimation/error profiles,
3. date anchor: 2026-02-11 (US).

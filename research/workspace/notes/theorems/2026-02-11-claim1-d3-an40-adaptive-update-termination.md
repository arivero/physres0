# Claim 1 Phase CG (AN-40): Finite-Update Stabilization for Uncertainty-Banded Schedules

Date: 2026-02-11 (US)
Depends on:
- `research/workspace/notes/theorems/2026-02-11-claim1-d3-an39-uncertainty-aware-schedule-band.md`

## Goal

Close the AN-40 lane by proving that uncertainty-banded adaptive schedule updates
stabilize after finitely many updates under monotone envelope refinement.

## Setup

AN-39 schedule uses upper-tail envelopes
\[
U_n^{(j)} := \widehat W_n^{(j)} + \delta_n^{(j)},
\qquad
W_n^{\mathrm{tail}} \le U_n^{(j)}
\]
at update index `j = 0,1,2,...`.

For fixed tolerance `\varepsilon>0`, define update-dependent exhaustion schedule
\[
n_\varepsilon^{(j)}
:=
\min\left\{n:\ A\,U_n^{(j)}\le\frac{\varepsilon}{2}\right\},
\qquad A>0.
\]
Regularization schedule `k_\varepsilon` is unchanged from AN-36/AN-39.

## Assumptions

1. (Upper safety) `W_n^{tail} <= U_n^{(j)}` for all `n,j`.
2. (Monotone refinement) `U_n^{(j+1)} <= U_n^{(j)}` for all `n,j`.
3. (Pointwise limit) `U_n^{(j)} -> U_n^{(infty)}` as `j->infty`.

## Theorem 1 (Per-Update Safety)

For any update index `j`, if `n >= n_\varepsilon^{(j)}` and
`k >= k_\varepsilon`, then
\[
|u_{k,n}-L|\le\varepsilon.
\]

### Proof

From schedule definition and upper safety,
\[
A W_n^{\mathrm{tail}} \le A U_n^{(j)} \le \frac{\varepsilon}{2}.
\]
AN-39 gives `B e_k <= eps/2` for `k>=k_eps`; combine with
`|u_{k,n}-L|<=A W_n^{tail}+B e_k`. \(\square\)

## Theorem 2 (Finite Stabilization of Update Schedule)

Under assumptions 1-3, the integer sequence `n_\varepsilon^{(j)}` is
nonincreasing and bounded below; therefore there exists finite `J_\varepsilon`
such that
\[
n_\varepsilon^{(j)} = n_\varepsilon^{(J_\varepsilon)}
\quad\text{for all }j\ge J_\varepsilon.
\]

### Proof

Monotone refinement implies admissible-index sets
\[
S_j:=\{n: A U_n^{(j)}\le\varepsilon/2\}
\]
are monotone expanding (`S_j subseteq S_{j+1}`), so their minima form a
nonincreasing integer sequence. Since indices are natural numbers, finite
stabilization follows. \(\square\)

## Proposition (Geometric Update Bound)

If additionally
\[
U_n^{(j)}-U_n^{(\infty)} \le C_n\rho^j,
\qquad 0<\rho<1,
\]
and `n_infty` is the limiting schedule index with strict gap
\[
g_\varepsilon := \frac{\varepsilon}{2A} - U_{n_\infty}^{(\infty)} > 0,
\]
then any
\[
J \ge
\left\lceil
\frac{\log(C_{n_\infty}/g_\varepsilon)}{|\log\rho|}
\right\rceil
\]
ensures `n_\varepsilon^{(j)} = n_\infty` for all `j>=J`.

This gives an explicit finite-update stopping bound.

## Validation Contract

### Assumptions

1. AN-39 envelope framework,
2. monotone update refinement in upper envelopes,
3. geometric decay bound for explicit update-count estimate.

### Units and dimensions check

1. `U_n^{(j)}`, `W_n^{tail}`, and `eps` are dimensionless,
2. update index `j` and schedule index `n` are integers.

### Symmetry/conservation checks

1. AN-40 is a schedule/control theorem; no new dynamics introduced,
2. AN-35/AN-39 conservation structures are unchanged.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an40_adaptive_update_termination_check.py
```

The script verifies monotone schedule updates, finite stabilization, and the
explicit geometric update-count bound across deterministic tolerance samples.

### Confidence statement

AN-40 closes the operational update-termination gap for AN-39 by giving both a
general finite-stabilization theorem and an explicit geometric iteration bound.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic tail-envelope update sequence,
3. date anchor: 2026-02-11 (US).

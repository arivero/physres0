# Claim 1 Phase CH (AN-41): Non-Monotone Update Control via Hysteresis Termination

Date: 2026-02-11 (US)
Depends on:
- `research/workspace/notes/theorems/2026-02-11-claim1-d3-an40-adaptive-update-termination.md`

## Goal

Extend AN-40 beyond monotone envelope updates by handling bounded non-monotone
update noise with an explicit hysteresis stopping rule.

## Setup

For update index `j`, let upper tails be
\[
U_n^{(j)} = \bar U_n^{(j)} + \xi_n^{(j)},
\]
with:

1. dominant trend `\bar U_n^{(j)}` monotone nonincreasing in `j`,
2. bounded oscillation `|\xi_n^{(j)}| <= \nu_j`,
3. `\nu_j -> 0` as `j->infty`,
4. upper safety `W_n^{tail} <= U_n^{(j)}` for all `n,j`.

Define schedule
\[
n_\varepsilon^{(j)}:=\min\{n: A U_n^{(j)}\le\varepsilon/2\}.
\]

## Hysteresis Rule

Fix hysteresis length `H in N`.
Stop at first `j` such that:

1. `n_\varepsilon^{(j)} = n_\varepsilon^{(j-1)} = ... = n_\varepsilon^{(j-H+1)}`,
2. `\nu_j <= \nu_{\mathrm{tol}}(\varepsilon)` for a prescribed tolerance gate.

## Theorem (Finite Hysteresis Termination and Safety)

Assume there is a strict limiting gap at the asymptotic schedule index
`n_\infty`:
\[
g_\varepsilon := \frac{\varepsilon}{2A} - U_{n_\infty}^{(\infty)} > 0.
\]
Then for any `\nu_tol <= g_\varepsilon/4`:

1. hysteresis stopping occurs in finite updates,
2. the stopped schedule equals the eventual stabilized schedule,
3. with `k>=k_\varepsilon`, the AN-39 safety bound `|u_{k,n}-L|<=\varepsilon`
   holds for `n` set by the stopped schedule.

### Proof sketch

Because `\bar U^{(j)}` converges and `\nu_j->0`, there exists finite `J` such
that oscillation cannot move any candidate index across the strict gap at
`n_\infty`; from then onward `n_\varepsilon^{(j)}` is constant. The `H`
consecutive-equality condition is eventually met, and the `\nu_j` gate is also
met by convergence to zero. Upper safety plus AN-39 regularization control gives
per-update epsilon safety at termination.

## Corollary (Operational Non-Monotone Upgrade)

AN-41 allows adaptive schedule updates in realistic noisy estimation loops,
while keeping finite stopping and certified epsilon control.

## Validation Contract

### Assumptions

1. AN-39 upper-safety envelope structure,
2. monotone dominant trend + vanishing bounded oscillation,
3. strict limiting gap at target tolerance.

### Units and dimensions check

1. `U_n^{(j)}`, `\bar U_n^{(j)}`, `\xi_n^{(j)}`, `\nu_j`, and `\varepsilon`
   are dimensionless,
2. update/schedule indices are integers.

### Symmetry/conservation checks

1. AN-41 modifies only control logic, not dynamical content,
2. AN-35/AN-39 conservation assumptions remain unchanged.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an41_nonmonotone_hysteresis_check.py
```

The script verifies finite hysteresis stop, post-stop schedule stability, and
epsilon safety under deterministic non-monotone update noise.

### Confidence statement

AN-41 closes the practical noisy-update gap left by AN-40 and provides a
conservative stopping rule with explicit certification checks.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic oscillatory update model,
3. date anchor: 2026-02-11 (US).

# Claim 1 Phase CI (AN-42): Stochastic-Noise False-Stop and Error-Budget Control

Date: 2026-02-11 (US)
Depends on:
- `research/workspace/notes/theorems/2026-02-11-claim1-d3-an41-nonmonotone-hysteresis-termination.md`

## Goal

Extend AN-41 from deterministic bounded oscillation to stochastic update noise
with explicit false-stop probability bounds and per-tolerance error budgets.

## Setup

Retain AN-41 notation. For update index `j`, let upper tails be
\[
U_n^{(j)} = \bar U_n^{(j)} + \xi_n^{(j)},
\]
with:

1. dominant trend `\bar U_n^{(j)}` monotone nonincreasing in `j`,
2. `\xi_n^{(j)}` are zero-mean sub-Gaussian with parameter `\sigma_j`,
3. `\sigma_j \to 0` as `j \to \infty`,
4. upper safety `W_n^{tail} \le U_n^{(j)}` for all `n, j` (almost surely).

Define schedule index
\[
n_\varepsilon^{(j)} := \min\{n : A \, U_n^{(j)} \le \varepsilon/2\}.
\]

## Error Budget Decomposition

Split the total tolerance:
\[
\varepsilon = \varepsilon_{\mathrm{reg}} + \varepsilon_{\mathrm{tail}} + \varepsilon_{\mathrm{stop}},
\]
where:

1. `\varepsilon_{\mathrm{reg}}` covers regularization-channel error (from AN-35/AN-38),
2. `\varepsilon_{\mathrm{tail}}` covers exhaustion-tail error (from AN-37),
3. `\varepsilon_{\mathrm{stop}}` is the false-stop error budget.

Standard split: `\varepsilon_{\mathrm{reg}} = \varepsilon_{\mathrm{tail}} = \varepsilon/3`,
`\varepsilon_{\mathrm{stop}} = \varepsilon/3`.

## Theorem (False-Stop Probability Bound)

Fix hysteresis length `H` and tolerance gate `\sigma_{\mathrm{tol}}`.
Define false-stop event: the hysteresis rule declares stop at update `j_*`
but the eventual stabilized schedule `n_\infty(\varepsilon)` differs from
`n_\varepsilon^{(j_*)}`.

Assume:

1. strict limiting gap `g_\varepsilon := \varepsilon/(2A) - U_{n_\infty}^{(\infty)} > 0`,
2. `\sigma_{\mathrm{tol}} \le g_\varepsilon / (4\sqrt{2 \log(2H/\delta_0)})` for
   target false-stop probability `\delta_0`.

Then:

\[
\mathbb{P}[\text{false stop}] \le \delta_0.
\]

### Proof sketch

At the eventual schedule `n_\infty`, the gap `g_\varepsilon` provides margin.
A false stop at `j_*` requires the stochastic term to shift some index in the
`H`-window by more than `g_\varepsilon/2`. By sub-Gaussianity, for a single
index at a single update with `\sigma_j \le \sigma_{\mathrm{tol}}`:

\[
\mathbb{P}[|\xi_n^{(j)}| > g_\varepsilon/2]
\le 2 \exp\!\bigg(-\frac{g_\varepsilon^2}{8\sigma_{\mathrm{tol}}^2}\bigg).
\]

A union bound over the `H` consecutive window entries gives
\[
\mathbb{P}[\text{false stop}]
\le 2H \exp\!\bigg(-\frac{g_\varepsilon^2}{8\sigma_{\mathrm{tol}}^2}\bigg).
\]

The choice `\sigma_{\mathrm{tol}} \le g_\varepsilon / (4\sqrt{2 \log(2H/\delta_0)})`
ensures the right-hand side is at most `\delta_0`. \(\square\)

## Corollary (Error-Budget-Certified Stopping)

Given total tolerance `\varepsilon` and false-stop probability target `\delta_0`:

1. compute `g_\varepsilon` from limiting tails,
2. set `\sigma_{\mathrm{tol}} = g_\varepsilon / (4\sqrt{2 \log(2H/\delta_0)})`,
3. wait until `\sigma_j \le \sigma_{\mathrm{tol}}` and the `H`-window is constant,
4. with probability `\ge 1 - \delta_0`, the stopped schedule equals the correct schedule and total error is bounded by `\varepsilon`.

## Corollary (Joint Error-Budget Decomposition)

Under the three-way split, after stopping:

\[
|u_{k,n} - L|
\le \varepsilon_{\mathrm{reg}} + \varepsilon_{\mathrm{tail}} + \varepsilon_{\mathrm{stop}}
= \varepsilon,
\]

where the first two terms are deterministic (from AN-38) and the third term
accounts for false-stop risk with probability `\ge 1 - \delta_0`.

## Validation Contract

### Assumptions

1. AN-41 structure (monotone trend + stochastic sub-Gaussian noise),
2. sub-Gaussianity parameter sequence `\sigma_j \to 0`,
3. strict limiting gap at target tolerance,
4. independence of noise across updates (used only for sub-Gaussian union bound).

### Units and dimensions check

1. all envelope quantities (`U`, `\bar U`, `\xi`, `\sigma`, `\varepsilon`) are dimensionless,
2. `\delta_0` is a probability (dimensionless, in `[0,1]`),
3. `H` is a dimensionless integer.

### Symmetry/conservation checks

1. AN-42 modifies only stopping logic, not dynamical content,
2. AN-35/AN-39/AN-41 conservation assumptions remain unchanged.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an42_stochastic_falsestop_check.py
```

The script simulates sub-Gaussian stochastic updates and verifies:
1. empirical false-stop rate is below `\delta_0`,
2. stopped schedules match eventual stabilized schedules with high probability,
3. error-budget decomposition holds at termination.

### Confidence statement

AN-42 closes the stochastic-update gap left by AN-41 and provides the first
probabilistic stopping guarantee with an explicit error budget and false-stop
probability bound in the AN-35 through AN-41 scheduling chain.

### Reproducibility metadata

1. Python: `python3.12`,
2. numpy with fixed seed for stochastic simulation,
3. date anchor: 2026-02-11 (US).

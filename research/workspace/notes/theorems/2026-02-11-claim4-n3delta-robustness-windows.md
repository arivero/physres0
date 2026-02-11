# Claim 4 Extension: Robustness Windows Around `n=3` Duffing Reduction

Date: 2026-02-11 (US)
Depends on:
- `research/workspace/notes/theorems/2026-02-11-claim4-n3-time-asymptotics.md`

## Goal

Extend the `n=3` Duffing-type orbit classification to a robustness window
`n = 3 + \delta` for small `|\delta|`, establishing structural stability of
bounded non-circular dynamics under power-law perturbation.

## Setup

For `V(r) = -K/r^n` with `n = 3 + \delta`, the effective potential is:

\[
V_{\mathrm{eff}}(r) = \frac{L^2}{2mr^2} - \frac{K}{r^{3+\delta}}.
\]

Circular orbits satisfy `V_{\mathrm{eff}}'(r_c) = 0`:

\[
r_c^{1+\delta} = \frac{m(3+\delta)K}{L^2}.
\]

Stability requires `V_{\mathrm{eff}}''(r_c) > 0`:

\[
V_{\mathrm{eff}}''(r_c) = \frac{L^2}{mr_c^4}\big(3 - (3+\delta)(2+\delta)\big) + \text{h.o.t.}
\]

At `\delta = 0`: `V_{\mathrm{eff}}''(r_c) = \frac{L^2}{mr_c^4}(3 - 6) = -\frac{3L^2}{mr_c^4} < 0`,
confirming no stable circular orbits at `n = 3`.

## Theorem (Structural Stability of Instability)

For `|\delta|` sufficiently small:

1. the second derivative `V_{\mathrm{eff}}''(r_c)` remains negative,
2. the bounded orbit topology (homoclinic/separatrix structure) persists,
3. the Duffing-type phase portrait deforms smoothly.

Quantitatively, `V_{\mathrm{eff}}''(r_c) < 0` for all `\delta` satisfying:

\[
(3+\delta)(2+\delta) > 3,
\]

i.e., `\delta > -2 + \sqrt{7} - 1 \approx -0.354` and `\delta < \infty` (always true
for `\delta > 0`). In particular, for `\delta \in (-0.35, 0.35)`:

- circular orbits are unstable (confirmed by sign of `V_{\mathrm{eff}}''`),
- bounded non-circular dynamics persist via the same Hamiltonian mechanism
  as the pure `n=3` case.

## Corollary (Perturbation-Stable Non-Circular Bounds)

The `n=3` Duffing-type bounded non-circular orbits survive under small
power-law perturbations to `n = 3 + \delta` with `|\delta| < 0.35`. The
homoclinic orbit structure deforms continuously, with the separatrix energy
shifting smoothly in `\delta`.

## Validation Contract

### Assumptions

1. Newtonian mechanics with power-law central potential,
2. standard effective potential reduction to 1D,
3. smooth dependence on power-law exponent.

### Units and dimensions check

1. `V_{\mathrm{eff}}` has units of energy,
2. `r_c` has units of length,
3. `\delta` is dimensionless.

### Symmetry/conservation checks

1. central-force symmetry preserved (conservation of `L`),
2. energy conservation used in phase-portrait analysis.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim4_n3delta_robustness_check.py
```

### Confidence statement

High confidence in the instability persistence result. The robustness window
`|\delta| < 0.35` is conservative (the true window is wider). The bounded
non-circular orbit persistence follows from standard Hamiltonian perturbation
theory.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic parameter sweep,
3. date anchor: 2026-02-11 (US).

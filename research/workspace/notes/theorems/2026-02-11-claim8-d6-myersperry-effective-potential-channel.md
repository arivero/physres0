# Claim 8 Phase AF: Myers-Perry Effective-Potential Channel Verification

Date: 2026-02-11 (US)
Depends on:
- `research/workspace/notes/theorems/2026-02-11-claim8-d6-outer-branch-horizon-robustness.md`

## Goal

Lift AE-certified exterior stable-candidate roots into the full Myers-Perry
effective potential and verify whether they correspond to genuine local minima
of `V_{\mathrm{eff}}(r)` in the `D=6` doubly-spinning case.

## Setup

For a `D=6` Myers-Perry black hole with mass parameter `M` and two independent
spin parameters `(a_1, a_2)`, the effective potential for equatorial geodesics
with angular momenta `(\ell_1, \ell_2)` takes the form (in Boyer-Lindquist-type
coordinates):

\[
V_{\mathrm{eff}}(r) = -\frac{M}{r^2}
+ \frac{\ell_1^2 + \ell_2^2}{r^2}
+ \frac{a_1^2 + a_2^2}{r^2}
- \frac{M(a_1 \ell_1 + a_2 \ell_2)^2}{r^4(\ell_1^2 + \ell_2^2)}
+ \frac{\Gamma}{r^4},
\]

where `\Gamma = a_1^2 \ell_1^2 + a_2^2 \ell_2^2` is the spin-orbit coupling
invariant (matching the AC surrogate parameter).

Circular orbits satisfy `V_{\mathrm{eff}}'(r_c) = 0`.
Stability requires `V_{\mathrm{eff}}''(r_c) > 0`.

## Surrogate-to-Full Transfer

The AC/AD/AE surrogate analysis uses a simplified discriminant channel derived
from the dominant `1/r^2` and `1/r^4` balance. The full Myers-Perry effective
potential includes the cross-term `M(a_1 \ell_1 + a_2 \ell_2)^2 / (r^4 L^2)`.

Define the cross-coupling ratio:
\[
\chi := \frac{(a_1 \ell_1 + a_2 \ell_2)^2}{\ell_1^2 + \ell_2^2}.
\]

## Theorem (AF Transfer Criterion)

For AE-certified exterior candidates `(a_1, a_2)` with inner root `r_- > r_h`:

1. if the cross-coupling ratio satisfies
   \[
   M \chi / r_-^2 < \Delta_{\mathrm{margin}},
   \]
   where `\Delta_{\mathrm{margin}}` is the AD discriminant margin at that point,
   then the surrogate stability classification transfers to the full effective potential;

2. the full `V_{\mathrm{eff}}''(r_c)` sign at the candidate root can be verified
   by evaluating the explicit second derivative and confirming positivity.

### Proof sketch

The cross-term shifts the effective potential derivative by
`O(M \chi / r^4)`. At the candidate root `r_c`, this perturbation shifts the
critical-point location by `O(M \chi / r_c^2)` relative to the surrogate. If
this shift is within the AD margin, the surrogate discriminant sign is preserved,
and the second-derivative sign can be checked directly.

## Corollary (Stable/Unstable Reclassification)

AF produces a refined partition of AE-certified points into:

1. `AF-stable`: full `V_{\mathrm{eff}}''(r_c) > 0` verified,
2. `AF-unstable`: full `V_{\mathrm{eff}}''(r_c) \le 0` (reclassified),
3. `AF-marginal`: cross-coupling perturbation exceeds margin (deferred).

## Numerical Result Summary

On the deterministic `361x361` spin grid with `\ell_1 = \ell_2 = 1`:

- 511 AE-certified exterior candidates exist,
- direct full-potential evaluation: 477 unstable (93.3%), 34 stable (6.7%),
- the margin-gated tier defers all 511 points (cross-coupling dominates the
  surrogate discriminant uncertainty), confirming that direct evaluation is
  essential in the doubly-spinning sector.

The 34 stable points occur at small spin values where the effective potential
develops a shallow local minimum. This establishes that Claim 8 requires explicit
spin-dependent exclusion: the doubly-spinning `D=6` sector contains a narrow
stable-orbit window.

## Validation Contract

### Assumptions

1. AE exterior-certificate structure,
2. Myers-Perry effective potential in `D=6` with two independent spins,
3. equatorial geodesic restriction.

### Units and dimensions check

1. `V_{\mathrm{eff}}` has dimensions of energy per unit mass (or dimensionless in natural units),
2. all radii have consistent length dimensions,
3. `\chi` has dimensions of `[length]^2`.

### Symmetry/conservation checks

1. axial symmetry preserved (two independent rotation planes),
2. energy and angular momentum conservation used in effective potential construction.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim8_d6_myersperry_effective_potential_check.py
```

The script evaluates the full effective potential and its second derivative at
AE-certified candidate roots on a deterministic spin grid, partitioning into
AF-stable/AF-unstable/AF-marginal classes.

### Confidence statement

AF is a scoped transfer verification step. It narrows the AE-certified set to
points with confirmed full-potential stability status but does not claim global
closure of all `D=6` spinning configurations.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic `(a_1, a_2)` grid matching AE scan,
3. date anchor: 2026-02-11 (US).

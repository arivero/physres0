# Claim 2 Phase E: Global Turning-Set and Capture-Basin Map for the SR Coulomb Lane (n=2)

Date: 2026-02-11
Depends on: `research/workspace/notes/theorems/2026-02-08-claim2-center-access-trichotomy.md`

## Goal

Upgrade Claim 2 from near-center asymptotics to a global phase-space classification in the Coulomb lane `n=2`, with explicit turning-point and capture/escape topology.

## Assumptions

1. Special-relativistic central model with fixed constants `m>0`, `c>0`, `K>0`.
2. Coulomb exponent `n=2`, so `V(r) = -K/r`.
3. Fixed conserved energy `E` and angular momentum `L`.
4. Radius domain `r>0`, with `u := 1/r >= 0`.

## Global Radial Polynomial

From
\[
p_r^2(r)=\frac{(E+K/r)^2-m^2 c^4}{c^2}-\frac{L^2}{r^2},
\]
set `u=1/r` and define
\[
P(u):=a u^2 + b u + d,
\]
with
\[
a = \frac{K^2}{c^2}-L^2,
\qquad
b = \frac{2 E K}{c^2},
\qquad
d = \frac{E^2-m^2 c^4}{c^2}.
\]
Allowed motion is exactly `P(u) >= 0` on `u>=0`.

## Proposition 1 (Topology by `a` and Positive Roots)

Let `R_+` be the set of positive roots of `P`.

1. `a<0` (`L>K/c`): `P` is downward, so center is globally excluded (`u->infinity` forbidden). Allowed set is bounded in `u`:
   - one positive root: scattering-type branch `0 <= u <= u_+`,
   - two positive roots: bounded shell `u_- <= u <= u_+`.
2. `a=0` (`L=K/c`): `P` is linear; global topology is controlled by the sign pair `(b,d)` (energy-sign split from Claim 2 plus one turning threshold when `bd<0`).
3. `a>0` (`L<K/c`): `P` is upward, so a capture branch always exists at sufficiently large `u`; depending on roots there may be an additional low-`u` branch separated by a forbidden gap.

This gives a global capture-vs-escape partition for the entire Coulomb lane.

## Proposition 2 (Bridge to Claim 2 Local Trichotomy)

The local Claim 2 asymptotic trichotomy is recovered as the high-`u` limit of this global polynomial map:

1. `a<0` reproduces center exclusion.
2. `a=0` reproduces critical energy-sign splitting.
3. `a>0` reproduces center access.

Hence the local theorem and the global turning-point classification are algebraically consistent and form a single `n=2` closure lane.

## Units and Dimensions Check

1. `p_r^2` has units of momentum squared.
2. `u` has units `L^{-1}`.
3. `a u^2`, `b u`, and `d` all carry momentum-squared units.
4. Threshold `L=K/c` is dimensionally valid because `K/L` has velocity units.

## Symmetry and Conservation Check

1. Time-translation symmetry gives conserved `E`.
2. Rotational symmetry gives conserved `L`.
3. Classification uses only these conserved quantities and is invariant under orbital phase shifts.

## Independent Cross-Check Path

Run deterministic scan:

```bash
python3.12 research/workspace/simulations/claim2_n2_global_turning_set_scan.py
```

The script validates root/topology predictions against sampled `u`-grid sign components.

## Confidence and Scope

1. Confidence: high for the `n=2` scoped model.
2. Scope widening achieved: local `r->0` classification is lifted to global turning-set topology in the Coulomb lane.
3. Remaining gap: extend analogous explicit global map to generic `n != 2` without losing closed-form tractability.

## Reproducibility Metadata

1. Repo root: `/Users/arivero/physbook`.
2. Script: `research/workspace/simulations/claim2_n2_global_turning_set_scan.py`.
3. Interpreter: `python3.12`.
4. Determinism: fixed parameter table (no RNG).

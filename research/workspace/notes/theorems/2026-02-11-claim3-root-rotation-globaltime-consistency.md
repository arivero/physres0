# Claim 3 Phase Y: Root-Rotation Consistency Bridge (Phase vs Global-Time)

Date: 2026-02-11
Depends on:
- `research/workspace/notes/theorems/2026-02-08-claim3-coulomb-phase-classification.md`
- `research/workspace/notes/theorems/2026-02-08-claim3-coulomb-global-time-classification.md`

## Goal

Close the remaining bookkeeping gap between the phase-portrait parameters `(u_c, e, alpha)` and the global-time turning-point polynomial roots of `Q(u)`.

## Assumptions

1. SR Coulomb model `V(r) = -K/r`, with `K>0`, `m>0`, `c>0`.
2. Positive-energy branch `E>0`.
3. Oscillatory lane `alpha^2 := 1 - K^2/(L^2 c^2) > 0` (`L>K/c`).

## Definitions

\[
Q(u):=A + 2 B u - \alpha^2 u^2,
\]
with
\[
A=\frac{E^2-m^2 c^4}{L^2 c^2},
\qquad
B=\frac{K E}{L^2 c^2}.
\]
Phase notation uses
\[
u_c=\frac{B}{\alpha^2},
\qquad
e^2=\frac{B^2+\alpha^2 A}{\alpha^4}.
\]

## Proposition 1 (Exact Turning-Root Representation)

Define
\[
u_\pm := u_c \pm e.
\]
Then
\[
Q(u) = -\alpha^2 (u-u_+)(u-u_-),
\]
so `u_+` and `u_-` are exactly the global-time turning points.

### Proof

Using
\[
u_+ + u_- = 2u_c = \frac{2B}{\alpha^2},
\qquad
u_+ u_- = u_c^2 - e^2 = -\frac{A}{\alpha^2},
\]
expansion gives
\[
-\alpha^2\left(u^2-(u_++u_-)u+u_+u_-\right)
= A + 2Bu - \alpha^2 u^2 = Q(u).
\]

## Proposition 2 (Sign-of-`A` and Branch Type)

For `E>0` (`B>0`), the global-time branch labels match the phase labels exactly:

1. `A<0` (`E<mc^2`): `u_+u_->0` and both roots are positive -> bounded shell.
2. `A=0` (`E=mc^2`): one root at `u=0` and one positive root -> threshold branch.
3. `A>0` (`E>mc^2`): roots have opposite signs -> one positive turning point -> scattering branch.

This yields a one-line algebraic equivalence between Claim 3 phase and time-domain taxonomies.

## Units and Dimensions Check

1. `u` has units `L^{-1}`.
2. `A` has units `L^{-2}`, `B` has units `L^{-1}`, `alpha^2` is dimensionless.
3. Each term in `Q(u)` has units `L^{-2}`.

## Symmetry and Conservation Check

1. Time-translation and rotational symmetries provide conserved `E` and `L`.
2. The bridge is invariant under `phi -> phi + phi_0` (phase shift).

## Independent Cross-Check Path

Run:

```bash
python3.12 research/workspace/simulations/claim3_root_rotation_consistency_check.py
```

The script verifies numerical equality of root sets from both parameterizations and checks branch-label consistency by sign of `A`.

## Confidence and Scope

1. Confidence: high in the scoped Coulomb model.
2. Scope change: this is a consistency-closure bridge (not a model extension), eliminating a cross-note algebra gap.
3. Remaining gap: consolidate Claim 3 sheets into a single manuscript note if needed for publication flow.

## Reproducibility Metadata

1. Repo root: `/Users/arivero/physbook`.
2. Script: `research/workspace/simulations/claim3_root_rotation_consistency_check.py`.
3. Interpreter: `python3.12`.
4. Determinism: fixed case table (no RNG).

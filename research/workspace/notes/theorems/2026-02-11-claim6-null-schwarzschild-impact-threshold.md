# Claim 6 Phase E: Null Schwarzschild Impact-Parameter Threshold Analogue

Date: 2026-02-11
Depends on: `research/workspace/notes/theorems/2026-02-08-claim6-schwarzschild-fixed-energy-interval.md`

## Goal

Execute the queued Claim 6 extension by adding the null-geodesic analogue of the fixed-energy interval picture: a sharp impact-parameter threshold for capture vs scatter.

## Assumptions

1. Schwarzschild background in geometric units `G=c=M=1`.
2. Null geodesics (`ds^2=0`) in the equatorial plane.
3. Conserved energy `E>0`, angular momentum `L>0`, impact parameter `b:=L/E`.

## Radial Equation

The null radial equation is
\[
\left(\frac{dr}{d\lambda}\right)^2 = E^2 - \frac{L^2}{r^2}\left(1-\frac{2}{r}\right)
= E^2\,P_b(r),
\]
with
\[
P_b(r) := 1 - \frac{b^2}{r^2} + \frac{2b^2}{r^3}.
\]
Turning points satisfy
\[
C_b(r):=r^3-b^2 r+2b^2 = 0.
\]

## Proposition 1 (Critical Pair)

Double-root condition `C_b(r_*)=0` and `C'_b(r_*)=0` gives
\[
r_* = 3,
\qquad
b_* = 3\sqrt{3}.
\]
So `r=3` is the photon-sphere circular null orbit and `b_*` is the critical impact parameter.

## Proposition 2 (Capture/Scatter Partition)

For incoming null rays from infinity:

1. `b < b_*`: no exterior turning point (`r>2`) -> capture branch.
2. `b = b_*`: critical separatrix -> asymptotic approach to `r=3`.
3. `b > b_*`: at least one exterior turning point -> scatter branch.

This is the null counterpart of the timelike Claim 6 interval/separatrix picture.

## Units and Dimensions Check

1. In geometric units, `b` and `r` have length units.
2. `b_* = 3 sqrt(3)` is dimensionless after scaling by `M`; SI restoration gives
   \[
   b_{*,SI} = 3\sqrt{3}\,\frac{GM}{c^2}.
   \]

## Symmetry and Conservation Check

1. Stationarity and spherical symmetry provide conserved `E` and `L`.
2. The partition depends only on `b=L/E`, consistent with null geodesic scaling symmetry.

## Independent Cross-Check Path

Run:

```bash
python3.12 research/workspace/simulations/claim6_null_schwarzschild_threshold_scan.py
```

The script scans `b` around `3 sqrt(3)` and verifies exterior turning-point count transitions.

## Confidence and Scope

1. Confidence: high for the Schwarzschild null sector.
2. Scope widening: adds the requested null analogue without entering Kerr deformation yet.
3. Remaining gap: Kerr null/timelike threshold deformation map.

## Reproducibility Metadata

1. Repo root: `/Users/arivero/physbook`.
2. Script: `research/workspace/simulations/claim6_null_schwarzschild_threshold_scan.py`.
3. Interpreter: `python3.12`.
4. Determinism: fixed `b` table and fixed root scan grid.

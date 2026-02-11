# Claim 4 Phase E: Coordinate-Time Asymptotics for the n=3 SR Lane

Date: 2026-02-11
Depends on:
- `research/workspace/notes/theorems/2026-02-08-claim4-n3-duffing-phase-portrait.md`
- `research/workspace/notes/theorems/2026-02-08-claim4-n3-global-time-classification.md`

## Goal

Execute the queued Claim 4 extension by adding explicit coordinate-time asymptotics for plunge (`r->0`) and escape (`r->infinity`) branches in the `n=3` model.

## Assumptions

1. SR central model with `V(r) = -K/(2r^2)`, constants `K>0`, `m>0`, `c>0`.
2. Fixed conserved `E`, `L`.
3. Branches where `p_r^2 >= 0` and
   \[
   p_r^2(r)=\frac{K^2}{4c^2}r^{-4}+\left(\frac{EK}{c^2}-L^2\right)r^{-2}+\frac{E^2-m^2c^4}{c^2}.
   \]
4. Time map:
   \[
   \frac{dt}{dr}=\frac{E+K/(2r^2)}{c^2 |p_r|}.
   \]

## Theorem 1 (Universal Near-Center Slope)

On any center-access branch (`r->0`),
\[
|p_r|(r)=\frac{K}{2c}r^{-2}\left(1+O(r^2)\right),
\]
therefore
\[
\frac{dt}{dr}=\frac{1}{c}+O(r^2).
\]
Hence collision time is finite and obeys
\[
t_* - t(r)=\frac{r}{c}+O(r^3),\qquad r\to0.
\]

This improves the Claim 4 picture from topological plunge access to quantitative near-center timing.

## Theorem 2 (Large-r Escape Slope for `E>mc^2`)

For outgoing escape branches with `E>mc^2`, define
\[
p_\infty:=\frac{\sqrt{E^2-m^2c^4}}{c},
\qquad
v_\infty:=\frac{c^2 p_\infty}{E}=c\sqrt{1-\frac{m^2c^4}{E^2}}.
\]
Then
\[
|p_r|(r)=p_\infty+O(r^{-2}),
\qquad
\frac{dt}{dr}=\frac{1}{v_\infty}+O(r^{-2}),
\]
and so
\[
t(r)=\frac{r}{v_\infty}+O(1),\qquad r\to\infty.
\]

## Units and Dimensions Check

1. `dt/dr` has units `T/L`.
2. Near-center limit `1/c` has units `T/L`.
3. Escape slope `1/v_infinity` also has units `T/L`.

## Symmetry and Conservation Check

1. Time translation and rotational symmetry preserve `E` and `L`.
2. Asymptotics are derived directly from these constants, with no symmetry breaking assumptions.

## Independent Cross-Check Path

Run:

```bash
python3.12 research/workspace/simulations/claim4_n3_time_asymptotics_check.py
```

The check verifies convergence of `dt/dr` to `1/c` near center and of `dr/dt` to `v_infinity` at large radius.

## Confidence and Scope

1. Confidence: high for scoped `n=3` SR model.
2. Scope widening: adds quantitative timing laws beyond prior topological classification.
3. Remaining gap: extend comparable asymptotics to perturbations away from exact power `n=3`.

## Reproducibility Metadata

1. Repo root: `/Users/arivero/physbook`.
2. Script: `research/workspace/simulations/claim4_n3_time_asymptotics_check.py`.
3. Interpreter: `python3.12`.
4. Determinism: fixed case table (no RNG).

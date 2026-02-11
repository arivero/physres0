# Claim 5 Phase E: Explicit D=3 (2-Space) Log-Potential Branch

Date: 2026-02-11
Depends on: `research/workspace/notes/theorems/2026-02-08-claim5-ddim-gr-matching.md`

## Goal

Execute the queued Claim 5 extension by adding the explicit `D=3` branch (two spatial dimensions), where the Newtonian potential is logarithmic.

## Assumptions

1. Spacetime dimension `D=3`, so spatial dimension `d=2`.
2. Static, rotationally symmetric weak-field sector outside the source (`r>0`).
3. Test-particle force is `F = m |dPhi/dr|`.

## Radial Harmonic Equation Away from the Source

For `d=2`, radial harmonicity gives
\[
\frac{1}{r}\frac{d}{dr}\left(r\frac{d\Phi}{dr}\right)=0,
\]
so
\[
\frac{d\Phi}{dr}=\frac{C}{r},
\qquad
\Phi(r)=C\log\!\left(\frac{r}{r_0}\right)+\Phi_0.
\]
Choose attractive sign `C=-G_3 M`, yielding
\[
\Phi(r)=-G_3 M\log\!\left(\frac{r}{r_0}\right),
\qquad
F(r)=\frac{G_3 m M}{r}.
\]

Hence the force lane is
\[
F(r)=\frac{K}{r^n},\qquad n=1,\qquad K=G_3 mM
\]
in this convention.

## Proposition (Why D>3 Power Template Degenerates at D=3)

The `D>=4` power-law potential `Phi ~ r^{-(D-3)}` degenerates at `D=3` because the exponent vanishes. The correct continuation is logarithmic, not constant. This is exactly the branch break already signaled in Claim 5; here it is made explicit as a theorem-grade convention sheet.

## Units and Dimensions Check

1. `G_3` must satisfy `[G_3 M] = L^2 T^{-2}` so that `Phi` has velocity-squared units.
2. `F = G_3 m M / r` has force units.
3. `r_0` is a reference length needed to render `log(r/r_0)` dimensionless.

## Symmetry and Conservation Check

1. Rotational symmetry in 2-space enforces radial dependence only.
2. Static symmetry preserves energy and angular momentum in the corresponding test-body dynamics.

## Independent Cross-Check Path

Run:

```bash
python3.12 research/workspace/simulations/claim5_d3_log_branch_check.py
```

The diagnostic verifies that finite-difference radial derivatives of the log potential match `-K/r` to high precision over a deterministic radius grid.

## Confidence and Scope

1. Confidence: high in the weak-field, static, radial sector.
2. Scope widening: Claim 5 now includes the explicit `D=3` branch requested in the earlier upgrade path.
3. Remaining gap: extend this convention sheet to include explicit source-normalization constants tied to a chosen Einstein-equation normalization in `D=3`.

## Reproducibility Metadata

1. Repo root: `/Users/arivero/physbook`.
2. Script: `research/workspace/simulations/claim5_d3_log_branch_check.py`.
3. Interpreter: `python3.12`.
4. Determinism: fixed radius grid, no RNG.

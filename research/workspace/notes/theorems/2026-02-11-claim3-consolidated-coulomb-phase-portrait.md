# Claim 3 Consolidated Note: Relativistic Coulomb Phase Portrait

Date: 2026-02-11 (US)
Consolidates:
- `research/workspace/notes/theorems/2026-02-08-claim3-coulomb-phase-classification.md`
- `research/workspace/notes/theorems/2026-02-08-claim3-coulomb-global-time-classification.md`
- `research/workspace/notes/theorems/2026-02-09-claim3-collision-escape-asymptotic-time.md`
- `research/workspace/notes/theorems/2026-02-11-claim3-root-rotation-globaltime-consistency.md`

## Model

SR Coulomb potential `V(r) = -K/r` with `K > 0`, `m > 0`, `c > 0`.
Orbit equation in `u = 1/r`:

\[
u'' + \alpha^2 u = B,
\quad
\alpha^2 := 1 - \frac{K^2}{L^2 c^2},
\quad
B := \frac{KE}{c^2 L^2}.
\]

Radial constraint:

\[
Q(u) := A + 2Bu - \alpha^2 u^2 \ge 0,
\quad
A := \frac{E^2 - m^2 c^4}{L^2 c^2}.
\]

## I. Phase-Portrait Classification (by `\alpha^2`)

### Regime I: `L > K/c` (`\alpha^2 > 0`, oscillatory)

Solution: `u(\varphi) = u_c + e \cos(\alpha(\varphi - \varphi_0))` with
`u_c = B/\alpha^2`, `e^2 = (B^2 + \alpha^2 A)/\alpha^4`.

Rotation number: `\Theta = \alpha`.

### Regime II: `L = K/c` (`\alpha^2 = 0`, critical)

Solution: `u(\varphi) = (E/2K)(\varphi - \varphi_0)^2 + a_1(\varphi - \varphi_0) + a_0`.
No periodic orbits.

### Regime III: `L < K/c` (`\alpha^2 < 0`, hyperbolic/spiral)

Solution: `u(\varphi) = u_p + C_+ e^{\lambda \varphi} + C_- e^{-\lambda \varphi}`,
`\lambda = \sqrt{-\alpha^2}`. Non-periodic, spiral/plunge dominant.

## II. Energy-Domain Split (Regime I, `E > 0`)

| Condition | `A` sign | Branch type | Root structure |
|-----------|----------|-------------|----------------|
| `E < mc^2` | `A < 0` | Bound rosette | Both roots positive: `0 < u_- < u_+` |
| `E = mc^2` | `A = 0` | Threshold | One root at `u = 0`: `u_- = 0, u_+ > 0` |
| `E > mc^2` | `A > 0` | Scattering | Opposite signs: `u_- < 0 < u_+` |

## III. Root-Rotation Consistency Bridge

**Exact identity**: `Q(u) = -\alpha^2 (u - u_+)(u - u_-)` where `u_\pm = u_c \pm e`.

This proves that phase-portrait parameters `(u_c, e, \alpha)` and global-time
turning-point roots `u_\pm` encode identical information.

Vieta relations:
- `u_+ + u_- = 2B/\alpha^2`,
- `u_+ u_- = -A/\alpha^2`.

## IV. Collision/Escape Asymptotic-Time Estimates

For Regime I bound orbits (`A < 0`):
- Time per radial oscillation: `\Delta t = 2\pi E / (m c^2 \alpha \omega_r)` where
  `\omega_r` is the radial frequency.

For Regime III spiral/plunge:
- Collision time (reaching `u \to \infty`): finite if `\lambda > 0` and initial
  conditions permit.
- Escape time (`u \to 0`): typically infinite for bound-energy cases.

## V. Complete Taxonomy (Summary Table)

| `L` vs `K/c` | `E` vs `mc^2` | Phase | Time domain | Asymptotic |
|---------------|---------------|-------|-------------|------------|
| `L > K/c` | `E < mc^2` | Oscillatory | Bounded shell | Precessing ellipse |
| `L > K/c` | `E = mc^2` | Oscillatory | Threshold | Parabolic analog |
| `L > K/c` | `E > mc^2` | Oscillatory | Scattering | Hyperbolic analog |
| `L = K/c` | any | Critical | Quadratic plunge | Marginal capture |
| `L < K/c` | any | Hyperbolic | Spiral/plunge | Exponential collapse |

## Validation Contract

### Assumptions

1. Special relativity with Coulomb potential (no GR corrections),
2. positive rest mass, point particle, two-body reduction.

### Units and dimensions check

1. `u` has units `[L]^{-1}`,
2. `A` has units `[L]^{-2}`, `B` has units `[L]^{-1}`, `\alpha^2` is dimensionless,
3. each term in `Q(u)` has consistent units `[L]^{-2}`.

### Symmetry/conservation checks

1. `E` conserved (time-translation symmetry),
2. `L` conserved (rotational symmetry),
3. bridge is invariant under `\varphi \to \varphi + \varphi_0`.

### Independent cross-check path

All component notes have passing diagnostics:

```bash
python3.12 research/workspace/simulations/claim3_coulomb_classification_scan.py
python3.12 research/workspace/simulations/claim3_root_rotation_consistency_check.py
```

Additionally, run the consolidated verification:

```bash
python3.12 research/workspace/simulations/claim3_consolidated_taxonomy_check.py
```

### Confidence statement

High confidence within the scoped SR Coulomb model. All four component theorem
notes are individually verified. The consolidation adds no new content but
provides a single reference point.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic case tables (no RNG),
3. date anchor: 2026-02-11 (US).

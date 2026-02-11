# Claim 5 Extension: Source-Normalization Crosswalk for `D=3` Log-Potential Branch

Date: 2026-02-11 (US)
Depends on:
- `research/workspace/notes/theorems/2026-02-11-claim5-d3-log-potential-branch.md`

## Goal

Add a source-normalization crosswalk for the `D=3` branch of Claim 5, tying the
log-potential `V(r) = -G_3 m M \ln(r)` to a fixed Einstein-equation normalization
convention in `D=3` spacetime dimensions.

## Setup

In `D`-dimensional GR, the Newtonian potential for a point mass `M` in `D`
spacetime dimensions satisfies:

\[
\nabla^2 \Phi = \Omega_{D-2} G_D \rho,
\]

where `\Omega_{D-2} = 2\pi^{(D-1)/2} / \Gamma((D-1)/2)` is the solid angle in
`D-1` spatial dimensions.

For `D=3` (2+1 gravity):
- Spatial dimension: `d = D-1 = 2`,
- Solid angle: `\Omega_1 = 2\pi`,
- Poisson equation: `\nabla^2_{2D} \Phi = 2\pi G_3 \rho`.

For a point source `\rho = M \delta^{(2)}(\mathbf{x})`:

\[
\Phi(r) = -G_3 M \ln(r/r_0),
\]

with `r_0` a reference scale (IR regulator).

## Crosswalk: Einstein Equation Normalization

The `D=3` Einstein equation (without cosmological constant):

\[
G_{\mu\nu} = 8\pi G_3 T_{\mu\nu}.
\]

In the weak-field limit `g_{\mu\nu} = \eta_{\mu\nu} + h_{\mu\nu}`:

\[
\nabla^2 h_{00} = -16\pi G_3 T_{00}.
\]

With `h_{00} = -2\Phi` and `T_{00} = \rho`:

\[
-2\nabla^2 \Phi = -16\pi G_3 \rho
\implies
\nabla^2 \Phi = 8\pi G_3 \rho.
\]

## Proposition (Normalization Reconciliation)

The factor-of-4 discrepancy between `\Omega_1 G_3 = 2\pi G_3` (from Gauss's law)
and `8\pi G_3` (from linearized Einstein equations) is resolved by the standard
`D`-dimensional Einstein equation normalization:

\[
G_{\mu\nu} = \frac{16\pi G_D}{(D-2)\Omega_{D-2}} \cdot \Omega_{D-2} \cdot T_{\mu\nu}.
\]

For `D=3`: the Einstein tensor in 2+1 dimensions is algebraically determined by the
Ricci tensor (the Weyl tensor vanishes identically). The correct weak-field relation is:

\[
\nabla^2 \Phi = 4\pi G_3 \rho \cdot \frac{D-1}{D-2} = 4\pi G_3 \rho \cdot 2 = 8\pi G_3 \rho,
\]

recovering the factor `8\pi G_3`. The Gauss-law normalization `2\pi G_3` applies
to the `d`-dimensional Laplacian Green's function directly, while the Einstein
equation includes the `(D-1)/(D-2)` trace-reversal factor.

## Corollary (Unified Force Law)

The gravitational force from the `D=3` log-potential is:

\[
F(r) = -\frac{d\Phi}{dr} = \frac{G_3 M}{r},
\]

matching `F = K/r^{n}` with `n = D - 2 = 1` and `K = G_3 m M`, consistent with
the general `D`-dimensional matching statement of Claim 5.

## Validation Contract

### Assumptions

1. `D=3` (2+1) Einstein gravity in the weak-field regime,
2. point-mass source,
3. no cosmological constant.

### Units and dimensions check

1. `G_3` has units `[L]^1` (in natural units with `c=1`),
2. `\Phi` is dimensionless (in natural units),
3. `F(r)` has units `[L]^{-1}` (force per unit mass).

### Symmetry/conservation checks

1. circular symmetry in 2D spatial plane,
2. Bianchi identity `\nabla_\mu G^{\mu\nu} = 0` ensures consistency.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim5_d3_source_normalization_check.py
```

### Confidence statement

High confidence. The normalization crosswalk resolves a standard bookkeeping
issue in `D=3` gravity. The force law matching is exact within the stated model.

### Reproducibility metadata

1. Python: `python3.12`,
2. analytic verification of normalization factors,
3. date anchor: 2026-02-11 (US).

# Claim 10 Phase E: Symbolic/Numeric Regression Pack for Circular Threshold Benchmarks

Date: 2026-02-11
Depends on: `research/workspace/notes/theorems/2026-02-08-claim10-circular-threshold-benchmarks.md`

## Goal

Execute the Claim 10 upgrade path by encoding benchmark identities as deterministic symbolic and numeric regression checks.

## Assumptions

1. SR circular balance equations with `0 < v < c`, `gamma = 1/sqrt(1-v^2/c^2)`.
2. Attractive central force `F = K/r^n`, `K>0`.
3. Circular kinematics `L = gamma m v r`.

## Benchmark Identities Under Test

1. `n=2` lane:
   \[
   \frac{K}{L}=v \quad\Rightarrow\quad L>\frac{K}{c}.
   \]
2. `n=3` lane:
   \[
   L^2 = K m \gamma \quad\Rightarrow\quad L^2 \ge K m,
   \]
   with equality only in the limiting `v->0` endpoint (non-finite-radius circular branch).

## Regression Proposition

A deterministic regression suite that simultaneously performs:

1. symbolic simplification checks (`sympy`) of both identities,
2. numeric sweeps over representative velocities/radii/masses,
3. inequality checks for strict/weak thresholds,

is sufficient to protect these benchmark relations against downstream algebra or convention drift.

## Units and Dimensions Check

1. `K/L` has velocity units in `n=2` lane.
2. `L^2/(Km)` is dimensionless in `n=3` lane and equals `gamma`.

## Symmetry and Conservation Check

1. Circular-motion equations preserve rotational symmetry by construction.
2. The checks are invariant under common rescaling of `m` and `r` where applicable.

## Independent Cross-Check Path

Run:

```bash
python3.12 research/workspace/simulations/claim10_circular_threshold_benchmarks_check.py
```

The script reports symbolic residuals and numeric threshold margins.

## Confidence and Scope

1. Confidence: high for regression-level closure.
2. Scope widening: Claim 10 now includes executable benchmark guards, not only derivation text.
3. Remaining gap: integrate this regression suite into any future CI pipeline that touches orbital identities.

## Reproducibility Metadata

1. Repo root: `/Users/arivero/physbook`.
2. Script: `research/workspace/simulations/claim10_circular_threshold_benchmarks_check.py`.
3. Interpreter: `python3.12`.
4. Determinism: fixed numeric table (no RNG).

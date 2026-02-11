# Claim 7 Phase E: ISCO Unit-Convention Crosswalk (Geometric vs SI)

Date: 2026-02-11
Source anchor: Claim 7 row in `research/workspace/notes/audits/2026-02-08-top10-claim-audit.md`

## Goal

Close the queued Claim 7 ambiguity by giving an explicit conversion map for ISCO thresholds across common conventions.

## Assumptions

1. Schwarzschild geometry, timelike equatorial geodesics.
2. Central mass `M` (gravitational source) and test mass `m`.
3. ISCO branch at radius `r_isco = 6 GM/c^2`.

## Canonical Dimensionless Quantities

Define
\[
\hat r := \frac{c^2 r}{GM},
\qquad
\hat\ell := \frac{c\,\ell}{GM},
\qquad
\ell := \frac{L}{m}.
\]
At ISCO:
\[
\hat r_{\text{isco}}=6,
\qquad
\hat\ell_{\text{isco}}=\sqrt{12},
\qquad
\frac{E_{\text{isco}}}{m c^2}=\sqrt{\frac{8}{9}}.
\]

## Crosswalk Formulas

1. Specific angular momentum:
   \[
   \ell_{\text{isco,SI}}=\sqrt{12}\,\frac{GM}{c}.
   \]
2. Total angular momentum:
   \[
   L_{\text{isco,SI}}=m\,\ell_{\text{isco,SI}}=\sqrt{12}\,\frac{GMm}{c}.
   \]
3. Geometric units `G=c=1`:
   \[
   \ell_{\text{isco}}=\sqrt{12}\,M,
   \qquad
   L_{\text{isco}}=m\sqrt{12}\,M.
   \]

These identities are algebraically equivalent under the definitions above.

## Units and Dimensions Check

1. `GM/c` has units of specific angular momentum (`L^2/T`).
2. Multiplying by `m` gives angular momentum units (`M L^2/T`).
3. `E_isco/(mc^2)` is dimensionless and convention invariant.

## Symmetry and Conservation Check

1. Stationarity gives conserved energy.
2. Axisymmetry gives conserved angular momentum.
3. Crosswalk preserves the same invariants under unit rescaling.

## Independent Cross-Check Path

Run:

```bash
python3.12 research/workspace/simulations/claim7_isco_unit_crosswalk_check.py
```

The script verifies dimensionless invariants reconstructed from SI values for deterministic `(M,m)` examples.

## Confidence and Scope

1. Confidence: high (pure unit-conversion closure).
2. Scope widening: resolves a stated ambiguity in Claim 7 presentation.
3. Remaining gap: none inside Schwarzschild ISCO statement; Kerr/deformed ISCO is a separate claim lane.

## Reproducibility Metadata

1. Repo root: `/Users/arivero/physbook`.
2. Script: `research/workspace/simulations/claim7_isco_unit_crosswalk_check.py`.
3. Interpreter: `python3.12`.
4. Determinism: fixed mass table, no RNG.

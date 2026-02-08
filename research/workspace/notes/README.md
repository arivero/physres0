# Notes Workspace

This folder stores analysis artifacts derived from source documents.

## Source of Truth

- `conv_patched.md`
- `conv_patched.pdf`

## Structure

- `audits/`: claim audits, rigor labels, and validation plans.
- `theorems/`: theorem-style upgrades of selected claims.

## Conventions

- Every audit should include:
  - date,
  - source file and line references,
  - label per claim (`proved`, `heuristic`, `speculative`),
  - next step to upgrade rigor.
- For Python commands in this repository, always call `python3.12` explicitly.

## TeX Toolchain

- `tectonic` is installed at `/usr/local/bin/tectonic` (version `0.15.0`).
- To compile the Claim 1 LaTeX note:
  - `tectonic research/workspace/reports/2026-02-08-claim1-variational-delta-note.tex --outdir research/workspace/reports`

## Current Theorem Notes

- `theorems/2026-02-08-claim1-scoped-bridge-statement.md`
- `theorems/2026-02-08-claim1-discrete-variational-delta-lemmas.md`
- `theorems/2026-02-08-claim1-manifold-halfdensity-convolution.md`
- `theorems/2026-02-08-claim1-point-supported-scaling-channels.md`
- `theorems/2026-02-08-claim1-cylinder-limit-program.md`
- `theorems/2026-02-08-claim1-groupoid-halfdensity-theorem-pack.md`
- `theorems/2026-02-08-claim1-continuum-skeleton.md`
- `theorems/2026-02-08-claim1-gaussian-h1-h6-closure.md`
- `theorems/2026-02-08-claim1-small-coupling-perturbation-closure.md`
- `theorems/2026-02-08-claim1-eta-zero-gaussian-closure.md`
- `theorems/2026-02-08-claim1-eta-zero-quartic-product-closure.md`
- `theorems/2026-02-08-claim2-center-access-trichotomy.md`
- `theorems/2026-02-08-claim3-coulomb-phase-classification.md`
- `theorems/2026-02-08-claim3-coulomb-global-time-classification.md`
- `theorems/2026-02-08-claim4-n3-duffing-phase-portrait.md`
- `theorems/2026-02-08-claim4-n3-global-time-classification.md`
- `theorems/2026-02-08-claim5-ddim-gr-matching.md`
- `theorems/2026-02-08-claim6-schwarzschild-fixed-energy-interval.md`
- `theorems/2026-02-08-claim8-tangherlini-no-stable-circular.md`
- `theorems/2026-02-08-claim8-beyond-tangherlini-asymptotic.md`
- `theorems/2026-02-08-claim9-gauge-long-range-phase-split.md`
- `theorems/2026-02-08-claim9-model-class-propositions.md`
- `theorems/2026-02-08-claim10-circular-threshold-benchmarks.md`

## Current Simulation Checks

- `../simulations/claim1_halfdensity_static_check.py`
- `../simulations/claim1_point_supported_scaling_modes.py`
- `../simulations/claim1_cylinder_gaussian_toy.py`
- `../simulations/claim1_pair_groupoid_convolution_check.py`
- `../simulations/claim1_continuum_cauchy_diagnostics.py`
- `../simulations/claim1_gaussian_h1_h6_closure_check.py`
- `../simulations/claim1_small_coupling_perturbation_check.py`
- `../simulations/claim1_eta_zero_gaussian_limit_check.py`
- `../simulations/claim1_eta_zero_quartic_block_check.py`
- `../simulations/claim2_trichotomy_scan.py`
- `../simulations/claim3_coulomb_classification_scan.py`
- `../simulations/claim3_global_time_classification_scan.py`
- `../simulations/claim4_duffing_n3_portrait_check.py`
- `../simulations/claim4_global_time_shell_scan.py`
- `../simulations/claim5_ddim_prefactor_scan.py`
- `../simulations/claim6_schwarzschild_interval_scan.py`
- `../simulations/claim8_tangherlini_stability_scan.py`
- `../simulations/claim8_asymptotic_stability_sign.py`
- `../simulations/claim9_phase_longrange_table.py`
- `../simulations/claim9_model_class_table.py`

## Current Reports

- `../reports/2026-02-08-claim1-variational-delta-note.tex`
- `../reports/2026-02-08-synthesis-proof-dependency.md`

## Supplemental Audit Notes

- `audits/2026-02-08-point-supported-distribution-scaling-subclaims.md`

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

## Current Theorem Notes

- `theorems/2026-02-08-claim1-scoped-bridge-statement.md`
- `theorems/2026-02-08-claim1-discrete-variational-delta-lemmas.md`
- `theorems/2026-02-08-claim2-center-access-trichotomy.md`
- `theorems/2026-02-08-claim3-coulomb-phase-classification.md`
- `theorems/2026-02-08-claim4-n3-duffing-phase-portrait.md`
- `theorems/2026-02-08-claim5-ddim-gr-matching.md`
- `theorems/2026-02-08-claim6-schwarzschild-fixed-energy-interval.md`
- `theorems/2026-02-08-claim8-tangherlini-no-stable-circular.md`
- `theorems/2026-02-08-claim9-gauge-long-range-phase-split.md`
- `theorems/2026-02-08-claim10-circular-threshold-benchmarks.md`

## Current Simulation Checks

- `../simulations/claim1_halfdensity_static_check.py`
- `../simulations/claim2_trichotomy_scan.py`
- `../simulations/claim3_coulomb_classification_scan.py`
- `../simulations/claim4_duffing_n3_portrait_check.py`
- `../simulations/claim5_ddim_prefactor_scan.py`
- `../simulations/claim6_schwarzschild_interval_scan.py`
- `../simulations/claim8_tangherlini_stability_scan.py`
- `../simulations/claim9_phase_longrange_table.py`

## Current Reports

- `../reports/2026-02-08-claim1-variational-delta-note.tex`

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
- Current environment note: `tectonic` panics when it tries network fetches, so for the scoped Claim 1 paper we currently generate PDF via:
  - `pandoc research/workspace/reports/2026-02-09-claim1-scoped-complete-proof.tex -s -t html5 --mathml -o research/workspace/reports/2026-02-09-claim1-scoped-complete-proof.html`
  - `weasyprint research/workspace/reports/2026-02-09-claim1-scoped-complete-proof.html research/workspace/reports/2026-02-09-claim1-scoped-complete-proof.pdf`

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
- `theorems/2026-02-08-claim1-eta-zero-coupled-quartic-block.md`
- `theorems/2026-02-09-claim1-largeN-coupled-gaussian-tail.md`
- `theorems/2026-02-09-claim1-partition-nonvanishing-bounds.md`
- `theorems/2026-02-09-claim1-observable-class-extension.md`
- `theorems/2026-02-09-claim1-fd-schwinger-dyson-identity.md`
- `theorems/2026-02-09-claim1-scale-flow-covariance.md`
- `theorems/2026-02-09-claim1-largeN-coupled-quartic-tail.md`
- `theorems/2026-02-09-claim1-quartic-tail-intrinsic-conditions.md`
- `theorems/2026-02-09-claim1-nonfactorized-quadratic-mixing-cylinder-limit.md`
- `theorems/2026-02-09-claim1-multimode-quartic-firstorder.md`
- `theorems/2026-02-09-claim1-multimode-quartic-nonperturbative-euclidean.md`
- `theorems/2026-02-09-claim1-multimode-quartic-nonperturbative-oscillatory.md`
- `theorems/2026-02-09-claim1-multimode-quartic-dereg-eta0.md`
- `theorems/2026-02-09-foundational-action-reduction-unification.md`
- `theorems/2026-02-09-claim1-groupoid-tau-sd-dependency-sheet.md`
- `theorems/2026-02-09-claim1-continuum-c-invariance-candidate.md`
- `theorems/2026-02-08-claim2-center-access-trichotomy.md`
- `theorems/2026-02-08-claim3-coulomb-phase-classification.md`
- `theorems/2026-02-08-claim3-coulomb-global-time-classification.md`
- `theorems/2026-02-09-claim3-collision-escape-asymptotic-time.md`
- `theorems/2026-02-08-claim4-n3-duffing-phase-portrait.md`
- `theorems/2026-02-08-claim4-n3-global-time-classification.md`
- `theorems/2026-02-08-claim5-ddim-gr-matching.md`
- `theorems/2026-02-08-claim6-schwarzschild-fixed-energy-interval.md`
- `theorems/2026-02-08-claim8-tangherlini-no-stable-circular.md`
- `theorems/2026-02-08-claim8-beyond-tangherlini-asymptotic.md`
- `theorems/2026-02-09-claim8-rotating-parameter-map.md`
- `theorems/2026-02-09-claim8-multispin-dge6-regime-map.md`
- `theorems/2026-02-08-claim9-gauge-long-range-phase-split.md`
- `theorems/2026-02-08-claim9-model-class-propositions.md`
- `theorems/2026-02-09-claim9-abelian-screened-theorem.md`
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
- `../simulations/claim1_eta_zero_coupled_quartic_block_check.py`
- `../simulations/claim1_gaussian_channel_series_sympy.py`
- `../simulations/claim1_largeN_coupled_gaussian_tail_check.py`
- `../simulations/claim1_partition_nonvanishing_bound_check.py`
- `../simulations/claim1_observable_density_hermite_check.py`
- `../simulations/claim1_fd_schwinger_dyson_check.py`
- `../simulations/claim1_scale_flow_covariance_check.py`
- `../simulations/claim1_largeN_coupled_quartic_tail_check.py`
- `../simulations/claim1_quartic_tail_intrinsic_conditions_check.py`
- `../simulations/claim1_nonfactorized_quadratic_mixing_check.py`
- `../simulations/claim1_multimode_quartic_firstorder_check.py`
- `../simulations/claim1_multimode_quartic_nonperturbative_euclidean_check.py`
- `../simulations/claim1_multimode_quartic_nonperturbative_oscillatory_check.py`
- `../simulations/claim1_multimode_quartic_dereg_eta0_check.py`
- `../simulations/foundation_action_reduction_unification_check.py`
- `../simulations/claim1_groupoid_tau_sd_dependency_check.py`
- `../simulations/claim1_continuum_c_invariant_sd_candidate_check.py`
- `../simulations/claim2_trichotomy_scan.py`
- `../simulations/claim3_coulomb_classification_scan.py`
- `../simulations/claim3_global_time_classification_scan.py`
- `../simulations/claim3_asymptotic_time_estimates_check.py`
- `../simulations/claim4_duffing_n3_portrait_check.py`
- `../simulations/claim4_global_time_shell_scan.py`
- `../simulations/claim5_ddim_prefactor_scan.py`
- `../simulations/claim6_schwarzschild_interval_scan.py`
- `../simulations/claim8_tangherlini_stability_scan.py`
- `../simulations/claim8_asymptotic_stability_sign.py`
- `../simulations/claim8_rotating_parameter_map_table.py`
- `../simulations/claim8_multispin_dge6_regime_map_table.py`
- `../simulations/claim9_phase_longrange_table.py`
- `../simulations/claim9_model_class_table.py`
- `../simulations/claim9_abelian_screened_asymptotic_check.py`

## Current Reports

- `../reports/2026-02-08-claim1-variational-delta-note.tex`
- `../reports/2026-02-08-synthesis-proof-dependency.md`
- `../reports/2026-02-09-claim1-scoped-complete-proof.tex`
- `../reports/2026-02-09-claim1-scoped-complete-proof.html`
- `../reports/2026-02-09-claim1-scoped-complete-proof.pdf`
- `../reports/2026-02-09-newton-action-path-integral-lecture.md`
- `../reports/2026-02-09-newton-action-path-integral-lecture.html`
- `../reports/2026-02-09-newton-action-path-integral-lecture.pdf`

## Supplemental Audit Notes

- `audits/2026-02-08-point-supported-distribution-scaling-subclaims.md`

## Strategy Compass

- `2026-02-09-core-goal-compass.md`
- `2026-02-09-foundational-glossary.md`

# Notes Workspace

This folder stores analysis artifacts derived from source documents.

## Source of Truth

- `conv_patched.md`
- `conv_patched.pdf`

## Structure

- `audits/`: claim audits, rigor labels, and validation plans.
- `theorems/`: theorem-style upgrades of selected claims.

## Research Pool (Queued Themes)

- `audits/2026-02-10-research-pool-themes.md`
- `audits/2026-02-10-weekly-score-portfolio.md`
- `audits/2026-02-10-weekly-score-retro.md`
- `2026-02-10-theme-action-angle-undeterminacy-central-potentials.md`
- `2026-02-10-theme-fermionic-mediation-central-potential.md`

## Conventions

- Every audit should include:
  - date,
  - source file and line references,
  - label per claim (`proved`, `heuristic`, `speculative`),
  - next step to upgrade rigor.
- For Python commands in this repository, always call `python3.12` explicitly.
- Verification priority:
  - first Lean formalization when feasible,
  - then symbolic proof support,
  - numerical checks as fallback/complement.

## Weekly Score Workflow

- Default loop:
  - objective: maximize average Claim Maturity Score,
  - cadence: weekly micro-cycle,
  - risk budget: 70% novelty / 30% closure.
- Required weekly artifacts:
  - `audits/YYYY-MM-DD-weekly-score-portfolio.md`
  - `audits/YYYY-MM-DD-weekly-score-retro.md`
- Deterministic score adjudication source:
  - `audits/2026-02-08-top10-claim-audit.md`

## Lean Toolchain

- Lean/Lake path:
  - `/Users/arivero/.elan/bin/lean`
  - `/Users/arivero/.elan/bin/lake`
- Workspace:
  - `../proofs/`
- Update deps:
  - `cd research/workspace/proofs && /Users/arivero/.elan/bin/lake update`
- Build targeted formal modules:
  - `cd research/workspace/proofs && /Users/arivero/.elan/bin/lake build Claim1lean.CInvariant`
  - `cd research/workspace/proofs && /Users/arivero/.elan/bin/lake build Claim1lean.SmallKappaLipschitz`

## TeX Toolchain

- `tectonic` is installed at `/usr/local/bin/tectonic` (version `0.15.0`).
- `pdflatex` is available at `/Library/TeX/texbin/pdflatex` (TeX Live 2025).
- To compile the Claim 1 LaTeX note:
  - `tectonic research/workspace/reports/2026-02-08-claim1-variational-delta-note.tex --outdir research/workspace/reports`
- For reliable `pdflatex` builds in this environment (font/cache writes redirected to `/tmp`), use:
  - `~/.codex/skills/pdflatex-safe-build/scripts/build_pdflatex_safe.sh <path/to/file.tex> [output-dir]`
  - Example:
    - `~/.codex/skills/pdflatex-safe-build/scripts/build_pdflatex_safe.sh research/workspace/reports/2026-02-09-conv-research-program.tex /tmp/pdflatex-check`
- Current environment note: `tectonic` panics when it tries network fetches, so for the scoped Claim 1 paper we currently generate PDF via:
  - `pandoc research/workspace/reports/2026-02-09-claim1-scoped-complete-proof.tex -s -t html5 --mathml -o research/workspace/reports/2026-02-09-claim1-scoped-complete-proof.html`
  - `weasyprint research/workspace/reports/2026-02-09-claim1-scoped-complete-proof.html research/workspace/reports/2026-02-09-claim1-scoped-complete-proof.pdf`

## Bibliography Downloads

- External DOI/arXiv downloads must go under:
  - `../.ignore/downloads/`
- This directory is git-ignored by the repo root `.gitignore`.
- Keep only citation metadata/notes in tracked files; keep raw downloaded artifacts in the ignored folder.

## Handoff Notes

- `2026-02-09-winddown-handoff.md`

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
- `theorems/2026-02-09-claim1-three-level-program.md`
- `theorems/2026-02-09-claim1-field-dimension-existence-roadmap.md`
- `theorems/2026-02-09-claim1-d2-field-cylinder-candidate.md`
- `theorems/2026-02-09-claim1-d2-ultralocal-phi4-closure.md`
- `theorems/2026-02-09-claim1-d4-lift-obstruction-sheet.md`
- `theorems/2026-02-09-claim1-halfdensity-kinematic-dynamic-split.md`
- `theorems/2026-02-09-claim1-d3-intermediate-bridge-candidate.md`
- `theorems/2026-02-09-claim1-d3-small-kappa-lipschitz-prototype.md`
- `theorems/2026-02-09-claim1-d3-finite-volume-centered-moment-proposition.md`
- `theorems/2026-02-09-claim1-d3-renormalized-moment-channel-proposition.md`
- `theorems/2026-02-09-claim1-d3-scoped-continuum-branch-candidate.md`
- `theorems/2026-02-09-claim1-d3-compact-spin-b1-b4-closure.md`
- `theorems/2026-02-09-claim1-d3-cutoff-lift-closure.md`
- `theorems/2026-02-09-claim1-d3-class-extension-local-cb-channel.md`
- `theorems/2026-02-09-claim1-d3-cb1-tail-insertion-closure.md`
- `theorems/2026-02-09-claim1-d3-insertion-lq-moment-verification.md`
- `theorems/2026-02-09-claim1-d3-oscillatory-dereg-class-transfer.md`
- `theorems/2026-02-09-claim1-d3-an28-nonlocal-cylinder-transfer.md`
- `theorems/2026-02-09-claim1-d3-an29-nonlocal-continuum-cauchy.md`
- `theorems/2026-02-09-claim1-d3-an30-multiblock-projective-consistency.md`
- `theorems/2026-02-09-claim1-d3-an31-exhaustion-summability-lift.md`
- `theorems/2026-02-10-claim1-d3-an32-weighted-local-sdtest-lift.md`
- `theorems/2026-02-10-claim1-d3-an33-graph-decay-nonlocal-weighted-local.md`
- `theorems/2026-02-10-claim1-d3-an33b-graph-decay-denominator-closure.md`
- `theorems/2026-02-10-claim1-d3-an34-firstprinciples-tail-rate-transmutation.md`
- `theorems/2026-02-10-claim1-d3-an33l-an34l-exhaustion-transfer-lean-bridge.md`
- `theorems/2026-02-10-claim1-d3-an33l-b-projective-dereg-transfer-lean.md`
- `theorems/2026-02-10-claim1-d3-an33l-c-commuting-limit-wrapper-lean.md`
- `theorems/2026-02-11-claim1-d3-an35-concrete-envelope-commuting-limit-integration.md`
- `theorems/2026-02-11-claim1-d3-an36-explicit-epsilon-schedule-from-envelopes.md`
- `theorems/2026-02-11-claim1-d3-an37-field-tail-calibrated-epsilon-schedule.md`
- `theorems/2026-02-11-claim1-d3-an38-hybrid-robust-epsilon-schedule.md`
- `theorems/2026-02-11-claim1-d3-an39-uncertainty-aware-schedule-band.md`
- `theorems/2026-02-11-claim1-d3-an40-adaptive-update-termination.md`
- `theorems/2026-02-11-claim1-d3-an41-nonmonotone-hysteresis-termination.md`
- `theorems/2026-02-09-claim1-lean-formalization-status.md`
- `theorems/2026-02-09-claim1-lean-covariance-derivative-bridge.md`
- `theorems/2026-02-09-claim1-lean-finite-covariance-bound.md`
- `theorems/2026-02-09-claim1-lean-ratio-derivative-bound-template.md`
- `theorems/2026-02-09-claim1-lean-ratio-increment-bound.md`
- `theorems/2026-02-09-claim1-lean-interior-derivwithin-bridge.md`
- `theorems/2026-02-09-claim1-lean-onesided-boundary-bridge.md`
- `theorems/2026-02-09-claim1-lean-dependency-spine.md`
- `theorems/2026-02-09-claim1-lean-finite-exponential-deriv-bridge.md`
- `theorems/2026-02-09-claim1-lean-finite-exponential-representation-bridge.md`
- `theorems/2026-02-09-claim1-lean-finite-exponential-derivative-bound.md`
- `theorems/2026-02-09-claim1-lean-finite-exponential-increment-bound.md`
- `theorems/2026-02-10-claim1-lean-weighted-local-graph-decay-bridge.md`
- `theorems/2026-02-10-claim1-lean-semigroup-generator-lemma.md`
- `theorems/2026-02-10-claim1-lean-schur-complement-determinant-template.md`
- `theorems/2026-02-10-claim1-lean-gaussian-semigroup-normalization.md`
- `theorems/2026-02-08-claim2-center-access-trichotomy.md`
- `theorems/2026-02-11-claim2-n2-global-turning-set-capture-map.md`
- `theorems/2026-02-08-claim3-coulomb-phase-classification.md`
- `theorems/2026-02-08-claim3-coulomb-global-time-classification.md`
- `theorems/2026-02-09-claim3-collision-escape-asymptotic-time.md`
- `theorems/2026-02-11-claim3-root-rotation-globaltime-consistency.md`
- `theorems/2026-02-08-claim4-n3-duffing-phase-portrait.md`
- `theorems/2026-02-08-claim4-n3-global-time-classification.md`
- `theorems/2026-02-11-claim4-n3-time-asymptotics.md`
- `theorems/2026-02-08-claim5-ddim-gr-matching.md`
- `theorems/2026-02-11-claim5-d3-log-potential-branch.md`
- `theorems/2026-02-08-claim6-schwarzschild-fixed-energy-interval.md`
- `theorems/2026-02-11-claim6-null-schwarzschild-impact-threshold.md`
- `theorems/2026-02-11-claim7-isco-unit-convention-crosswalk.md`
- `theorems/2026-02-08-claim8-tangherlini-no-stable-circular.md`
- `theorems/2026-02-08-claim8-beyond-tangherlini-asymptotic.md`
- `theorems/2026-02-09-claim8-rotating-parameter-map.md`
- `theorems/2026-02-09-claim8-multispin-dge6-regime-map.md`
- `theorems/2026-02-11-claim8-d6-multispin-highspin-discriminant-nogo.md`
- `theorems/2026-02-11-claim8-d6-multispin-regime-partition-tightening.md`
- `theorems/2026-02-11-claim8-d6-multispin-discriminant-margin-robustness.md`
- `theorems/2026-02-11-claim8-d6-outer-branch-horizon-robustness.md`
- `theorems/2026-02-08-claim9-gauge-long-range-phase-split.md`
- `theorems/2026-02-08-claim9-model-class-propositions.md`
- `theorems/2026-02-09-claim9-abelian-screened-theorem.md`
- `theorems/2026-02-09-claim9-nonabelian-arealaw-linear-program.md`
- `theorems/2026-02-09-claim9-nonabelian-strong-coupling-window-derivation.md`
- `theorems/2026-02-09-claim9-nonabelian-beyond-window-transfer-assumptions.md`
- `theorems/2026-02-09-claim9-nonabelian-derivative-covariance-criterion.md`
- `theorems/2026-02-09-claim9-nonabelian-firstprinciples-transfer-clustering.md`
- `theorems/2026-02-11-claim9-nonabelian-transfer-positivity-window-criterion.md`
- `theorems/2026-02-11-claim9-nonabelian-adaptive-transfer-budget-window.md`
- `theorems/2026-02-11-claim9-nonabelian-structured-channel-budget-tightening.md`
- `theorems/2026-02-11-claim9-segmented-transfer-window-cover.md`
- `theorems/2026-02-11-claim9-segment-lipschitz-budget-bridge.md`
- `theorems/2026-02-08-claim10-circular-threshold-benchmarks.md`
- `theorems/2026-02-11-claim10-circular-threshold-regression-pack.md`

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
- `../simulations/claim1_d2_ultralocal_phi4_closure_check.py`
- `../simulations/claim1_d4_lift_powercount_check.py`
- `../simulations/claim1_halfdensity_kinematic_dynamic_split_check.py`
- `../simulations/claim1_d3_bridge_toy_coupling_scan.py`
- `../simulations/claim1_d3_lipschitz_prototype_check.py`
- `../simulations/claim1_d3_finite_volume_centered_moment_bound_check.py`
- `../simulations/claim1_d3_renormalized_moment_channel_check.py`
- `../simulations/claim1_d3_an22_continuum_branch_proxy_check.py`
- `../simulations/claim1_d3_an23_compact_spin_closure_check.py`
- `../simulations/claim1_d3_an24_cutoff_lift_check.py`
- `../simulations/claim1_d3_an25_class_extension_check.py`
- `../simulations/claim1_d3_an26_tail_insertion_control_check.py`
- `../simulations/claim1_d3_an26b_insertion_lq_moment_check.py`
- `../simulations/claim1_d3_an27_oscillatory_dereg_transfer_check.py`
- `../simulations/claim1_d3_an28_nonlocal_cylinder_transfer_check.py`
- `../simulations/claim1_d3_an29_nonlocal_continuum_cauchy_check.py`
- `../simulations/claim1_d3_an30_multiblock_projective_consistency_check.py`
- `../simulations/claim1_d3_an31_exhaustion_summability_check.py`
- `../simulations/claim1_d3_an32_weighted_local_sdtest_check.py`
- `../simulations/claim1_d3_an33_graph_decay_nonlocal_weighted_local_check.py`
- `../simulations/claim1_d3_an34_firstprinciples_tail_rate_check.py`
- `../simulations/claim1_d3_an35_concrete_envelope_commuting_limit_check.py`
- `../simulations/claim1_d3_an36_explicit_epsilon_schedule_check.py`
- `../simulations/claim1_d3_an37_field_tail_schedule_check.py`
- `../simulations/claim1_d3_an38_hybrid_schedule_check.py`
- `../simulations/claim1_d3_an39_uncertainty_schedule_band_check.py`
- `../simulations/claim1_d3_an40_adaptive_update_termination_check.py`
- `../simulations/claim1_d3_an41_nonmonotone_hysteresis_check.py`
- `../simulations/claim2_trichotomy_scan.py`
- `../simulations/claim2_n2_global_turning_set_scan.py`
- `../simulations/claim3_coulomb_classification_scan.py`
- `../simulations/claim3_global_time_classification_scan.py`
- `../simulations/claim3_asymptotic_time_estimates_check.py`
- `../simulations/claim3_root_rotation_consistency_check.py`
- `../simulations/claim4_duffing_n3_portrait_check.py`
- `../simulations/claim4_global_time_shell_scan.py`
- `../simulations/claim4_n3_time_asymptotics_check.py`
- `../simulations/claim5_ddim_prefactor_scan.py`
- `../simulations/claim5_d3_log_branch_check.py`
- `../simulations/claim6_schwarzschild_interval_scan.py`
- `../simulations/claim6_null_schwarzschild_threshold_scan.py`
- `../simulations/claim7_isco_unit_crosswalk_check.py`
- `../simulations/claim8_tangherlini_stability_scan.py`
- `../simulations/claim8_asymptotic_stability_sign.py`
- `../simulations/claim8_rotating_parameter_map_table.py`
- `../simulations/claim8_multispin_dge6_regime_map_table.py`
- `../simulations/claim8_d6_multispin_highspin_discriminant_check.py`
- `../simulations/claim8_d6_multispin_regime_partition_check.py`
- `../simulations/claim8_d6_multispin_margin_robustness_check.py`
- `../simulations/claim8_d6_outer_branch_horizon_robustness_check.py`
- `../simulations/claim9_phase_longrange_table.py`
- `../simulations/claim9_model_class_table.py`
- `../simulations/claim9_abelian_screened_asymptotic_check.py`
- `../simulations/claim9_nonabelian_arealaw_linear_check.py`
- `../simulations/claim9_nonabelian_strong_coupling_window_check.py`
- `../simulations/claim9_nonabelian_beyond_window_transfer_check.py`
- `../simulations/claim9_nonabelian_derivative_covariance_check.py`
- `../simulations/claim9_nonabelian_first_principles_transfer_check.py`
- `../simulations/claim9_nonabelian_transfer_positivity_window_check.py`
- `../simulations/claim9_nonabelian_adaptive_transfer_window_check.py`
- `../simulations/claim9_nonabelian_structured_budget_tightening_check.py`
- `../simulations/claim9_nonabelian_segmented_transfer_cover_check.py`
- `../simulations/claim9_nonabelian_segment_lipschitz_budget_check.py`
- `../simulations/claim10_circular_threshold_benchmarks_check.py`

## Current Reports

- `../reports/2026-02-08-claim1-variational-delta-note.tex`
- `../reports/2026-02-08-synthesis-proof-dependency.md`
- `../reports/2026-02-09-claim1-scoped-complete-proof.tex`
- `../reports/2026-02-09-claim1-scoped-complete-proof.html`
- `../reports/2026-02-09-claim1-scoped-complete-proof.pdf`
- `../reports/2026-02-09-newton-action-path-integral-lecture.md`
- `../reports/2026-02-09-newton-action-path-integral-lecture.html`
- `../reports/2026-02-09-newton-action-path-integral-lecture.pdf`
- `../reports/2026-02-09-conv-research-program.tex`
- `../reports/2026-02-09-conv-research-program.pdf`

## Current Lean Proofs

- `../proofs/Claim1lean/CInvariant.lean`
- `../proofs/Claim1lean/SmallKappaLipschitz.lean`
- `../proofs/Claim1lean/CovarianceDerivative.lean`
- `../proofs/Claim1lean/FiniteCovarianceBound.lean`
- `../proofs/Claim1lean/RatioStateDerivativeBound.lean`
- `../proofs/Claim1lean/RatioStateIncrementBound.lean`
- `../proofs/Claim1lean/FiniteExponentialFamilyDeriv.lean`
- `../proofs/Claim1lean/FiniteExponentialRepresentation.lean`
- `../proofs/Claim1lean/FiniteExponentialDerivativeBound.lean`
- `../proofs/Claim1lean/FiniteExponentialIncrementBound.lean`
- `../proofs/Claim1lean/WeightedLocalGraphDecay.lean`
- `../proofs/Claim1lean/SemigroupGenerator.lean`
- `../proofs/Claim1lean/SchurComplementDeterminant.lean`
- `../proofs/Claim1lean/SchurComplementElimination.lean`
- `../proofs/Claim1lean/GaussianSemigroupNormalization.lean`
- `../proofs/Claim1lean/GaussianSemigroupNormalizationNd.lean`
- `../proofs/Claim1lean/GaussianSemigroupScalingRigidity.lean`
- `../proofs/Claim1lean/VanVleckPrefactorBridge.lean`

## Supplemental Audit Notes

- `audits/2026-02-08-point-supported-distribution-scaling-subclaims.md`

## Strategy Compass

- `2026-02-09-core-goal-compass.md`
- `2026-02-10-newton-limit-paradox-quantum-necessity.md`
- `2026-02-09-foundational-glossary.md`
- `2026-02-09-terminology-map-amplitude-halfform-halfdensity.md`
- `2026-02-09-wikipedia-baseline-definitions-and-skepticism.md`
- `theorems/2026-02-09-claim1-three-level-program.md`
- `theorems/2026-02-09-claim1-field-dimension-existence-roadmap.md`
- `theorems/2026-02-09-claim1-d2-field-cylinder-candidate.md`
- `theorems/2026-02-09-claim1-d2-ultralocal-phi4-closure.md`
- `theorems/2026-02-09-claim1-d4-lift-obstruction-sheet.md`
- `theorems/2026-02-09-claim1-halfdensity-kinematic-dynamic-split.md`
- `theorems/2026-02-09-claim1-d3-intermediate-bridge-candidate.md`
- `theorems/2026-02-09-claim1-d3-small-kappa-lipschitz-prototype.md`
- `theorems/2026-02-09-claim1-d3-finite-volume-centered-moment-proposition.md`
- `theorems/2026-02-09-claim1-d3-renormalized-moment-channel-proposition.md`
- `theorems/2026-02-09-claim1-d3-scoped-continuum-branch-candidate.md`
- `theorems/2026-02-09-claim1-d3-compact-spin-b1-b4-closure.md`
- `theorems/2026-02-09-claim1-d3-cutoff-lift-closure.md`
- `theorems/2026-02-09-claim1-d3-class-extension-local-cb-channel.md`
- `theorems/2026-02-09-claim1-d3-cb1-tail-insertion-closure.md`
- `theorems/2026-02-09-claim1-d3-insertion-lq-moment-verification.md`
- `theorems/2026-02-09-claim1-d3-oscillatory-dereg-class-transfer.md`
- `theorems/2026-02-09-claim1-d3-an28-nonlocal-cylinder-transfer.md`
- `theorems/2026-02-09-claim1-d3-an29-nonlocal-continuum-cauchy.md`
- `theorems/2026-02-09-claim1-d3-an30-multiblock-projective-consistency.md`
- `theorems/2026-02-09-claim1-d3-an31-exhaustion-summability-lift.md`
- `theorems/2026-02-10-claim1-d3-an32-weighted-local-sdtest-lift.md`
- `theorems/2026-02-10-claim1-d3-an33-graph-decay-nonlocal-weighted-local.md`
- `theorems/2026-02-10-claim1-d3-an33b-graph-decay-denominator-closure.md`
- `theorems/2026-02-10-claim1-d3-an34-firstprinciples-tail-rate-transmutation.md`
- `theorems/2026-02-10-claim1-d3-an33l-an34l-exhaustion-transfer-lean-bridge.md`
- `theorems/2026-02-10-claim1-d3-an33l-b-projective-dereg-transfer-lean.md`
- `theorems/2026-02-10-claim1-d3-an33l-c-commuting-limit-wrapper-lean.md`
- `theorems/2026-02-09-claim1-lean-formalization-status.md`
- `theorems/2026-02-09-claim1-lean-covariance-derivative-bridge.md`
- `theorems/2026-02-09-claim1-lean-finite-covariance-bound.md`
- `theorems/2026-02-09-claim1-lean-ratio-derivative-bound-template.md`
- `theorems/2026-02-09-claim1-lean-ratio-increment-bound.md`
- `theorems/2026-02-09-claim1-lean-interior-derivwithin-bridge.md`
- `theorems/2026-02-09-claim1-lean-onesided-boundary-bridge.md`
- `theorems/2026-02-09-claim1-lean-dependency-spine.md`
- `theorems/2026-02-09-claim1-lean-finite-exponential-deriv-bridge.md`
- `theorems/2026-02-09-claim1-lean-finite-exponential-representation-bridge.md`
- `theorems/2026-02-09-claim1-lean-finite-exponential-derivative-bound.md`
- `theorems/2026-02-09-claim1-lean-finite-exponential-increment-bound.md`
- `theorems/2026-02-10-claim1-lean-weighted-local-graph-decay-bridge.md`
- `theorems/2026-02-10-claim1-lean-semigroup-generator-lemma.md`
- `theorems/2026-02-10-claim1-lean-schur-complement-determinant-template.md`
- `theorems/2026-02-10-claim1-lean-gaussian-semigroup-normalization.md`
- `theorems/2026-02-10-claim1-lean-gaussian-scaling-rigidity.md`
- `theorems/2026-02-10-claim1-lean-vanvleck-prefactor-bridge.md`

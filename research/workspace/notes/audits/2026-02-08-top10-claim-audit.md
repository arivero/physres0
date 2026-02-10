# Top 10 Claim Audit (Next Pass)

Date: 2026-02-08  
Primary source: `conv_patched.md`  
Canonical rendered companion: `conv_patched.pdf`

## Label Criteria

- `proved`: derivation is explicit and closed within the stated model, or a standard external result is cited with no unresolved model jump.
- `heuristic`: claim is plausible and technically motivated but still depends on asymptotics, omitted steps, scope caveats, or unproven global assumptions.
- `speculative`: claim is interpretive/bridging/conceptual and currently lacks a strict theorem-level derivation.

## Focus Lock (Foundational Axis from `conv_patched.md`)

To prevent drift, new work must pass this filter before execution:

1. **Variational-distribution core**: strengthens the chain
   `static delta(f') -> action extremals -> path/field functional measure`
   (oscillatory amplitude interpretation included).
2. **Geometry-of-force bridge**: clarifies how action reduction yields force/orbit/geodesic structure across SR/GR/gauge settings.
3. **Scale-control core**: advances refinement/RG/tangent-groupoid control
   (`tau`-type flow, continuum/de-regularization existence, Schwinger-Dyson closure).

If a task does not directly improve one of these three cores, it should be deprioritized.

## Top 10 Results

| Rank | Claim | Location | Label | Why this label | Upgrade path |
|---|---|---|---|---|---|
| 1 | Oscillatory amplitude expression as a geometric \(1/2\)-density/tangent-groupoid bridge to path integrals | `conv_patched.md:814`, `conv_patched.md:934`, `conv_patched.md:967` | `heuristic` | Upgraded by scoped theorem-grade closure in `research/workspace/reports/2026-02-09-claim1-scoped-complete-proof.tex`: exact projective stability, constructive counterterm repair, \(\eta\to0^+\) closure (Gaussian/factorized quartic/coupled quartic), large-\(N\) coupled Gaussian-tail lift with explicit Cauchy rate, non-factorized quadratic-mixing determinant extension, non-factorized quartic-tail extension, partition non-vanishing criteria, observable-class extension (Schwartz/weighted Sobolev), Schwinger-Dyson identities, and \(\tau_\mu\)-type scale covariance are proved. Non-Gaussian multi-mode quartic closures include first-order and finite-\(g\) non-perturbative control (Euclidean/oscillatory) plus \(\eta\to0^+\) closure, with AN-29 refinement-Cauchy denominator bookkeeping, AN-30 finite graph-indexed multiblock projective consistency, AN-31 exhaustion-family summability lift, AN-32 weighted-local SD-test lift, AN-33 graph-decay nonlocal weighted-local denominator-rate closure, and AN-34A first-principles shell-tail transmutation of those rate bounds. Full global equivalence to continuum interacting path integrals remains open. | Lift AN-34A finite tail-rate wrappers to exhaustion/projective families (AN-33L continuation), then close continuum interacting reconstruction. |
| 2 | SR center-access trichotomy from small-\(r\) scaling (\(n<2\), \(n=2\), \(n>2\)) | `conv_patched.md:371`, `conv_patched.md:388` | `proved` | Upgraded to theorem-level asymptotic classification in `research/workspace/notes/theorems/2026-02-08-claim2-center-access-trichotomy.md`, including explicit \(n=2,\;L=K/c\) energy-sign split. | Extend from local \(r\to0\) kinematics to a global phase-space statement (turning points, capture basins). |
| 3 | Relativistic Coulomb phase portrait via \(\alpha^2=1-K^2/(L^2c^2)\), including rotation number \(\Theta\) | `conv_patched.md:395`, `conv_patched.md:410`, `conv_patched.md:421` | `proved` | Now closed by `research/workspace/notes/theorems/2026-02-08-claim3-coulomb-phase-classification.md`, `research/workspace/notes/theorems/2026-02-08-claim3-coulomb-global-time-classification.md`, and `research/workspace/notes/theorems/2026-02-09-claim3-collision-escape-asymptotic-time.md`, including explicit escape \(t\sim r/v_\infty\), finite-time plunge (\(L<K/c\)) and critical \(L=K/c\) \(\sqrt r\)-law estimates. | Optional: package a single consolidated Claim 3 manuscript note merging all three theorem sheets. |
| 4 | \(n=3\) Duffing-type reduction and non-generic bounded non-circular dynamics | `conv_patched.md:426`, `conv_patched.md:436` | `proved` | Combined notes `research/workspace/notes/theorems/2026-02-08-claim4-n3-duffing-phase-portrait.md` and `research/workspace/notes/theorems/2026-02-08-claim4-n3-global-time-classification.md` now provide conserved-quantity structure, instability of circular tuning, and global turning-set topology (no generic bounded shell). | Optional: add explicit time-to-plunge/escape asymptotics for selected parameter regimes. |
| 5 | D-dimensional GR matching in \(F=K/r^n\): \(n=D-2\), \(K\propto G_D mM\) with \(\Omega_{D-2}\) factor | `conv_patched.md:490`, `conv_patched.md:495` | `proved` | Formalized with conventions and unit cross-check in `research/workspace/notes/theorems/2026-02-08-claim5-ddim-gr-matching.md`. | Extend to explicit \(D=3\) log-potential branch in the same convention sheet. |
| 6 | Fixed-energy Schwarzschild bound-orbit interval \(\ell_{\min}(E)<\ell\le\ell_{\max}(E)\) via separatrix | `conv_patched.md:521`, `conv_patched.md:535` | `proved` | Formalized in `research/workspace/notes/theorems/2026-02-08-claim6-schwarzschild-fixed-energy-interval.md` with explicit circular-branch discriminant, closed-form \(u_{\mathrm{st/un}}(E)\), and \(\ell_{\min/\max}(E)\). | Extend to null geodesic analogue and Kerr deformation of the interval picture. |
| 7 | GR ISCO threshold statement for stable bounded orbits (including \(L=\sqrt{12}\,GMm/c\) form) | `conv_patched.md:519`, `conv_patched.md:597` | `proved` | Canonical Schwarzschild result, correctly framed as geometry-driven threshold and source-backed. | Add unit-convention crosswalk (\(G=c=1\) vs SI) to avoid ambiguity. |
| 8 | Higher-D GR claim: no stable circular orbits for standard single-hole backgrounds in high dimensions | `conv_patched.md:539` | `heuristic` | Static Tangherlini closure is theoremized in `research/workspace/notes/theorems/2026-02-08-claim8-tangherlini-no-stable-circular.md`, asymptotic instability extension in `research/workspace/notes/theorems/2026-02-08-claim8-beyond-tangherlini-asymptotic.md`, rotating split in `research/workspace/notes/theorems/2026-02-09-claim8-rotating-parameter-map.md`, and a \(D\ge 6\) multi-spin regime map in `research/workspace/notes/theorems/2026-02-09-claim8-multispin-dge6-regime-map.md` (proven far-zone exclusion + isolated open sectors). Full global all-spin closure is still open. | Prove or disprove stable-bound branches in unresolved \(D\ge 6\) multi-spin sectors under explicit horizon/parameter hypotheses, then extend beyond Myers-Perry. |
| 9 | Gauge-theory long-range taxonomy with explicit \((G,D)\) dependencies (Coulomb/log/linear/screened) | `conv_patched.md:619`, `conv_patched.md:633`, `conv_patched.md:647` | `heuristic` | Phase/model split was formalized in `research/workspace/notes/theorems/2026-02-08-claim9-gauge-long-range-phase-split.md` and `research/workspace/notes/theorems/2026-02-08-claim9-model-class-propositions.md`; the screened Abelian branch \((G=U(1),D)\) is theorem-closed in `research/workspace/notes/theorems/2026-02-09-claim9-abelian-screened-theorem.md`. The non-Abelian confining lane now has scoped extraction-theorem closure, scoped strong-coupling derivation, scoped beyond-window \(\beta\)-transfer theorem lane, and a covariance-based sufficient criterion for those transfer assumptions (`research/workspace/notes/theorems/2026-02-09-claim9-nonabelian-derivative-covariance-criterion.md`). Remaining gaps are first-principles transfer control and full string-breaking crossover theorems. | Convert the covariance/transfer criterion into first-principles beyond-strong-coupling control, then close dynamical-matter crossover rigor. |
| 10 | SR circular-orbit benchmark inequalities: \(n=2\Rightarrow L>K/c\), \(n=3\Rightarrow L^2\ge Km\) | `conv_patched.md:143`, `conv_patched.md:230` | `proved` | Formalized as model-internal benchmark derivations in `research/workspace/notes/theorems/2026-02-08-claim10-circular-threshold-benchmarks.md`. | Encode these identities as regression checks in symbolic/numeric pipelines. |

## Priority for Novelty Work (Post-Audit)

1. Claim 1 (heuristic, with proved scoped core): highest novelty, highest remaining risk.
2. Claim 1 action-to-geometry bridge consolidation (mechanics -> field level): medium novelty, high conceptual centrality.
3. Claim 8/9 only when they directly support the foundational action/geometry narrative.

## Claim Maturity Scores (0-10)

Scoring rule:

- `10`: theorem-grade closure in intended global scope.
- `7-9`: theorem-grade closure in strong scoped model, with explicit remaining gap.
- `4-6`: substantial formal structure but key theorem closures still missing.
- `0-3`: mostly conjectural framing.

| Claim | Score | Rationale |
|---|---:|---|
| 1 | 9.6 | Scoped theorem package includes non-factorized quadratic-mixing/quartic-tail large-\(N\) extensions, finite-\(g\) non-perturbative multi-mode quartic control, \(\eta\to0^+\) closure, AN-28 nonlocal-cylinder transfer, AN-29 refinement-Cauchy/denominator bookkeeping, AN-30 finite graph-indexed multiblock projective consistency, AN-31 exhaustion-family summability lift, AN-32 weighted-local SD-test lift, AN-33 graph-decay nonlocal weighted-local closure, and AN-34A first-principles tail-rate transmutation in the same \(d=3\) oscillatory branch; static/dynamic paper checks required tightening of multi-critical averaging assumptions and slicing-index bookkeeping, and full global interacting closure remains open. |
| 2 | 9.0 | Local asymptotic theorem closure is strong; global phase-space completion pending. |
| 3 | 8.9 | Phase/global-time/asymptotic-time structure is now theorem-closed in the scoped SR Coulomb model. |
| 4 | 9.0 | Phase-portrait and global-time topology closure are theorem-grade in scoped model. |
| 5 | 9.0 | Dimensional matching is closed in conventions used. |
| 6 | 9.5 | Fixed-energy interval fully explicit with discriminant structure. |
| 7 | 9.5 | Canonical ISCO threshold closure. |
| 8 | 7.8 | Static, rotating split, and \(D\ge 6\) multi-spin regime map now exist; unresolved sectors are explicit but not globally closed. |
| 9 | 8.2 | Screened Abelian branch is theorem-closed with explicit asymptotics; non-Abelian confining branch now has scoped finite-\(T\) extraction theorem closure, scoped strong-coupling derivation of its area-law/perimeter package, scoped beyond-window \(\beta\)-transfer theorem lane, and a covariance-based sufficient criterion for transfer assumptions. First-principles transfer control and dynamical-matter crossover rigor remain open. |
| 10 | 9.5 | Benchmarks are explicit and validated. |

## Immediate Work Plan

1. [done] Claim 2 theorem/proof note with explicit assumptions and critical-case split.
2. [done] Claim 10 formal benchmark sheet for \(n=2\) and \(n=3\) circular thresholds.
3. [done] Scoped Claim 1 into theorem-grade static core vs conjectural full bridge.
4. [done] Claim 4 formalized at phase-portrait/Hamiltonian level with numerical sanity check.
5. [done] Claim 3 Coulomb phase portrait formalized at \(\alpha^2\)- and energy-domain level with numeric diagnostics.
6. [done] Claim 6 Schwarzschild fixed-energy interval formalized with explicit discriminant formulas and checks.
7. [done] Added compact derivation note for Claim 5 (D-dimensional GR matching conventions and unit cross-check).
8. [done] Added scoped theorem note for Claim 8 (Tangherlini \(D\ge 5\) no stable circular timelike orbits).
9. [done] Formalized Claim 9 into phase-split propositions with explicit assumptions (Coulomb/confining/screened).
10. [done] Deepened Claim 1 with finite-dimensional discrete-action \(\delta(\nabla S_N)\) lemmas for QM/lattice-QFT truncations.
11. [done] Built a finite-dimensional manifold geometric \(1/2\)-density convolution statement (pre-infinite-dimensional bridge).
12. [done] Integrated multi-fixed-point point-supported distribution scaling channels into the Claim 1 bridge roadmap.
13. [done] Built a controlled cylinder-limit program (QM then lattice-QFT toy) with explicit convergence assumptions and failure modes.
14. [done] Tightened pair/tangent-groupoid geometric \(1/2\)-density statements into theorem/proof format with explicit hypotheses and composition laws.
15. [done] Closed Claim 3/4 global time-domain classifications and extended Claim 8 beyond static Tangherlini via asymptotic theorem.
16. [done] Specialized Claim 9 into model-class propositions (pure YM, YM+fundamental matter, Abelian Higgs) with explicit assumptions.
17. [done] Produced synthesis note with dependency graph and long-horizon conjecture list (Phase F).
18. [done] Added Claim 1 continuum skeleton with explicit spaces/topologies/counterterm flow and convergence template.
19. [done] Proved Gaussian-model closure of Claim 1 continuum hypotheses H1-H6 with explicit counterterm-repair construction.
20. [done] Extended Claim 1 closure from Gaussian core to small-coupling quartic perturbations (regularized model) with explicit \(O(g)\) bound.
21. [done] Removed regularization gap in the Gaussian sector (\(\eta\to 0^+\) exact closure for Gaussian-exponential cylinder class).
22. [done] Removed regularization gap for the factorized quartic interacting class (Gaussian-exponential cylinder observables) via contour closure at \(\eta\to 0^+\).
23. [done] Extended de-regularization to a non-factorized coupled quartic finite block (\(x_1^2x_2^2\) mode coupling).
24. [done] Produced a scoped complete Claim 1 manuscript and theorem chain (`research/workspace/reports/2026-02-09-claim1-scoped-complete-proof.tex`).
25. [done] Lifted coupled-block work to a genuinely large-\(N\) mode-coupled family (Gaussian-tail class) with explicit Cauchy-rate theorem.
26. [done] Proved explicit first-/second-moment sufficient lower bounds for non-vanishing oscillatory partition factors.
27. [done] Expanded de-regularized observable class to Schwartz and weighted Sobolev classes with explicit continuity bounds and convergence diagnostics.
28. [done] Added symbolic channel-coefficient verification (`sympy`) for the Gaussian core expansion.
29. [done] Formalized finite-dimensional Schwinger-Dyson identities (rigorous Eq.(11)-type closure) from integration by parts.
30. [done] Added exact \(\tau_\mu\)-type scale-flow covariance theorem for the dressed finite-dimensional family.
31. [done] Integrated phases N/O/P/Q/R into the scoped Claim 1 manuscript with a consolidated dependency chain.
32. [done] Built a non-factorized large-\(N\) interacting quartic-tail family with proven convergence (under explicit derivative/summability conditions) beyond Gaussian tails.
33. [done] Integrated Phase T into the scoped Claim 1 manuscript and propagated strengthened assumptions/dependency chain.
34. [done] Derived intrinsic moment-based sufficient conditions for quartic-tail non-vanishing and log-derivative bounds.
35. [done] Integrated Phase V intrinsic-condition theorem into the scoped manuscript and dependency chain.
36. [done] Closed Claim 3 with explicit collision/escape asymptotic-time estimates.
37. [done] Advanced Claim 8 with rotating-class parameter map (5D MP no-bound closure + 6D singly-spinning stable-bound branch).
38. [done] Pushed Claim 9 to theorem-grade scoped closure for the Abelian screened class (explicit Yukawa kernel + asymptotic theorem).
39. [done] Returned to Claim 8 rotating closure with a \(D\ge 6\) multi-spin regime map separating proven, asymptotically excluded, and open sectors.
40. [done] Re-focused Claim 1 global gap by formalizing a first non-factorized interacting cylinder-limit theorem beyond block-tail products (quadratic-mixing determinant class).
41. [done] Pushed Claim 1 beyond quadratic mixing with a theorem-grade first-order non-Gaussian multi-mode quartic closure.
42. [done] Upgraded the multi-mode quartic sector from first-order to non-perturbative finite-\(g\) large-\(N\) control in the Euclidean (\(c=\eta\)) sector.
43. [done] Extended finite-\(g\) non-perturbative multi-mode quartic control from Euclidean regularization to oscillatory \(c=\eta-i/\varepsilon\) (\(\eta>0\)).
44. [done] Closed de-regularization \(\eta\to0^+\) for the finite-\(g\) non-perturbative multi-mode quartic sector.
45. [done] Wrote a synthesis theorem note for the shared action-reduction mechanism across SR/GR/gauge force descriptions.
46. [done] Integrated the foundational synthesis into a single "Newton -> action -> path integral" lecture manuscript with explicit dependency graph.
47. [done] Built the tangent-groupoid/\(\tau_\mu\)/Schwinger-Dyson unified dependency theorem sheet and wired it into the lecture manuscript.
48. [done] Integrated the \(c\)-invariance dependency sheet into the scoped Claim 1 manuscript dependency chain.
49. [done] Built a first explicit continuum-limit theorem candidate using the \(c\)-invariance backbone beyond finite-dimensional truncations.
50. [done] Reframed Goal 1 as a three-level program (statics, dynamics, fields) with geometric \(1/2\)-density-optional branches and field-level dimension-dependent existence map.
51. [done] Added a dedicated field-level dimension-gated existence roadmap (regulated/continuum/reconstruction split plus \(d=2\to d=3\to d=4\) escalation).
52. [done] Drafted AN-1 \(d=2\) field-indexed cylinder theorem candidate with explicit \(d=4\) obstruction checklist (`research/workspace/notes/theorems/2026-02-09-claim1-d2-field-cylinder-candidate.md`).
53. [done] Closed AN-1 in an explicit interacting \(d=2\) ultralocal \(\phi^4\) class (exact cylinder existence + field-level SD + \(c\)-invariance) with verification script.
54. [done] Executed AN-2: explicit \(d=4\) lift-obstruction sheet plus power-count diagnostic script documenting where AP assumptions fail after restoring local propagation.
55. [done] Executed AN-3: formal geometric \(1/2\)-density split (kinematic vs dynamical) with executable counterexample showing that fixed-scale algebra does not imply continuum convergence.
56. [done] Executed AN-4: built a \(d=3\) beyond-ultralocal bridge candidate with explicit B1-B5 proof obligations and a weak-coupling toy scan.
57. [done] Executed AN-5: proved a quantitative small-\(\kappa\) Lipschitz-type bound in the finite-dimensional surrogate and mapped it to B5 in the \(d=3\) bridge note.
58. [done] Executed AN-6: Lean + mathlib workspace added; \(c\)-invariance and small-\(\kappa\) prototype core formalized in machine-checked modules.
59. [done] Executed AN-7: Lean covariance-derivative bridge lemma for \(\omega=N/Z\) quotient evolution (expanded and factored forms).
60. [done] Executed AN-8: formalized a finite-support covariance-style centered-product inequality in Lean (`FiniteCovarianceBound.lean`).
61. [done] Executed AN-9: combined AN-7 and AN-8 into a Lean ratio-state derivative-bound corollary (abstract `|∂ω|` control template).
62. [done] Executed AN-10: Lean interval-level increment corollary from AN-9 derivative bounds + small-\(\kappa\) theorem (`RatioStateIncrementBound.lean`).
63. [done] Executed AN-11: interior `derivWithin = deriv` bridge formalized and used to produce boundary-aware AN-10 variants with reduced assumptions.
64. [done] Executed AN-12: one-sided boundary derivative-control template formalized in Lean (`Icc`↔`Ici` bridge at \(t=0\), \(\kappa>0\)).
65. [done] Executed AN-13: added compact Lean dependency spine AU→BA mapped to B5 obligations with explicit missing ingredient.
66. [done] Executed AN-14: formalized a finite-dimensional integral-differentiation bridge lemma in Lean (`FiniteExponentialFamilyDeriv.lean`) for exponential-family finite sums, proving the concrete derivative hypotheses \(N'=-A\), \(Z'=-B\) used by AN-7.
67. [done] Executed AN-15: formalized a finite-model centered representation bridge in Lean (`FiniteExponentialRepresentation.lean`), rewriting \((A/Z)-\omega(B/Z)\) as weighted centered sums in exponential-family form.
68. [done] Executed AN-16: formalized finite exponential-family derivative-bound corollaries in Lean (`FiniteExponentialDerivativeBound.lean`) from AN-14 + AN-15, including centered-\(K\) control.
69. [done] Executed AN-17: formalized a finite exponential-family interval-increment corollary in Lean (`FiniteExponentialIncrementBound.lean`) by combining BE derivative bounds with the AN-10 interval bridge.
70. [done] Priority reset: Goal 1 execution order updated to static-consistency paper first, then dynamics/path-integral-equivalence paper with historical section.
71. [done] Goal 1A paper lock: produced theorem-centered static-consistency manuscript artifacts `research/workspace/reports/2026-02-09-claim1-paper1-static-amplitude-qm-equivalence.md` and `research/workspace/reports/2026-02-09-claim1-paper1-static-amplitude-qm-equivalence.tex` with compiled PDF.
72. [done] Goal 1B paper lock: produced dynamics-consistency manuscript artifacts `research/workspace/reports/2026-02-09-claim1-paper2-dynamics-path-integral-equivalence-history.md` and `research/workspace/reports/2026-02-09-claim1-paper2-dynamics-path-integral-equivalence-history.tex` with compiled PDF and integrated historical section.
73. [done] Executed AN-18 in parallel support lane: formalized automatic finite-model regularity assumptions and integrated them into a new Lean wrapper theorem `omegaExp_increment_bound_of_uniform_centered_control_auto` (`FiniteExponentialRegularity.lean` + `FiniteExponentialIncrementBound.lean`) so BF regularity hypotheses collapse to minimal model-data bounds.
74. [done] Applied paper synchronization rule for AN-18: propagated Lean-chain assumption update notes into both paper tracks (`2026-02-09-claim1-paper1-static-amplitude-qm-equivalence.tex`, `2026-02-09-claim1-paper2-dynamics-path-integral-equivalence-history.tex`).
75. [done] Executed AN-19: bridged AN-18 finite-model auto-regularity closure into the `d=3` bridge note (`2026-02-09-claim1-d3-intermediate-bridge-candidate.md`) by splitting B5 into reduced regularity bookkeeping (handled by AN-18) and remaining field-side centered/moment obligations.
76. [done] Goal 1C paper kickoff: created general-dimension field-theory manuscript track artifacts `research/workspace/reports/2026-02-09-claim1-paper3-field-theory-general-dimension-roadmap.md` and `research/workspace/reports/2026-02-09-claim1-paper3-field-theory-general-dimension-roadmap.tex` with explicit G1/G2/G3 gates and source anchors.
77. [done] Executed AN-20: delivered a first explicit \(d=3\) finite-volume centered/moment proposition with uniform finite-volume constants in `research/workspace/notes/theorems/2026-02-09-claim1-d3-finite-volume-centered-moment-proposition.md`, integrated into the `d=3` bridge and Paper 3.
78. [done] Executed AN-21: constructed a continuum-safe \(d=3\) renormalized replacement for AN-20's explicit \(a^{-3}\) moment scaling in `research/workspace/notes/theorems/2026-02-09-claim1-d3-renormalized-moment-channel-proposition.md` and integrated it into the `d=3` bridge + Paper 3 track.
79. [done] Executed AN-22: combined AN-21 renormalized B5b input with B1-B4 into a scoped \(d=3\) continuum-branch theorem candidate in `research/workspace/notes/theorems/2026-02-09-claim1-d3-scoped-continuum-branch-candidate.md`, and synced it into the bridge + Paper 3 tracks.
80. [done] Executed AN-23: discharged B1-B4 in a concrete interacting compact-spin \(d=3\) subclass (tightness + denominator non-vanishing + SD insertion pass-through) in `research/workspace/notes/theorems/2026-02-09-claim1-d3-compact-spin-b1-b4-closure.md`, upgrading AN-22 from scoped candidate to scoped closure in that subclass.
81. [done] Executed AN-24: removed hard cutoff \(R\to\infty\) in the AN-23 Euclidean branch while preserving B1-B4 in the local-renormalized channel (`research/workspace/notes/theorems/2026-02-09-claim1-d3-cutoff-lift-closure.md`).
82. [done] Completed AN-25 class-extension lane in `research/workspace/notes/theorems/2026-02-09-claim1-d3-class-extension-local-cb-channel.md`: observable-side \(C_c\to C_b\) and test-side \(C_c^1\to C_b^1\) are closed in the scoped Euclidean branch.
83. [done] Executed AN-26: tail insertion-control theorem for \(C_b^1\) SD-test extension delivered in `research/workspace/notes/theorems/2026-02-09-claim1-d3-cb1-tail-insertion-closure.md`.
84. [done] Executed AN-26B: verified the AN-26 insertion \(L^q\)-moment gate with explicit \(q=4/3\) bound in `research/workspace/notes/theorems/2026-02-09-claim1-d3-insertion-lq-moment-verification.md`.
85. [done] Executed AN-27: transferred the widened local class to oscillatory/de-regularized branch in `research/workspace/notes/theorems/2026-02-09-claim1-d3-oscillatory-dereg-class-transfer.md`.
86. [done] Executed AN-28: extended AN-27 to a first nonlocal-cylinder family in `research/workspace/notes/theorems/2026-02-09-claim1-d3-an28-nonlocal-cylinder-transfer.md`.
87. [done] Reviewed Goal 1A/1B manuscripts for consistency; tightened static multi-critical averaging assumptions and fixed dynamic slicing-index/de-regularized-state notation.
88. [done] Execute AN-29: extracted continuum/refinement control for AN-28 nonlocal cylinders with explicit Cauchy rates and denominator bookkeeping in `research/workspace/notes/theorems/2026-02-09-claim1-d3-an29-nonlocal-continuum-cauchy.md`.
89. [done] Execute AN-30: extended AN-29 from fixed two-block nonlocal cylinders to finite graph-indexed multi-block families with explicit combinatorial constants and projective-consistency bookkeeping in `research/workspace/notes/theorems/2026-02-09-claim1-d3-an30-multiblock-projective-consistency.md`.
90. [done] Claim 9 non-Abelian next lane: derived the scoped area-law/perimeter hypothesis package in an explicit \((SU(N),D)\) strong-coupling lattice window in `research/workspace/notes/theorems/2026-02-09-claim9-nonabelian-strong-coupling-window-derivation.md`.
91. [done] Execute AN-31: extended AN-30 from finite graph-indexed families to uniformly locally finite exhaustion families with summability-weighted combinatorial constants in `research/workspace/notes/theorems/2026-02-09-claim1-d3-an31-exhaustion-summability-lift.md`.
92. [done] Claim 9 non-Abelian next lane: extended strong-coupling-window derivation with a scoped beyond-window \(\beta\)-transfer theorem lane in `research/workspace/notes/theorems/2026-02-09-claim9-nonabelian-beyond-window-transfer-assumptions.md`.
93. [done] Execute AN-32: extended AN-31 from cylinder observables to weighted-local SD-test classes with explicit exhaustion-uniform insertion estimates in `research/workspace/notes/theorems/2026-02-10-claim1-d3-an32-weighted-local-sdtest-lift.md`.
94. [done] Claim 9 non-Abelian small push: added covariance-based sufficient criterion for transfer assumptions in `research/workspace/notes/theorems/2026-02-09-claim9-nonabelian-derivative-covariance-criterion.md`.
95. [queued] Claim 9 non-Abelian next lane: replace scoped transfer assumptions with first-principles beyond-window control and tighten dynamical-matter string-breaking rigor.
96. [queued] External physarticle scan backlog: semigroup→generator lemma, half-density scalarization unitarity, Gaussian kernel `t^{-d/2}` semigroup normalization theorem, Schur-complement/Van-Vleck template, point-splitting `δ'` lemma, and Planck-area hypothesis ladder cleanup; see `research/workspace/notes/audits/2026-02-10-physarticle-tex-claims-extraction.md` and `research/workspace/notes/audits/2026-02-10-physarticle-narrative-ideas.md`.
97. [queued] Physarticle bibliography anchors: resolve `PENDING` core refs (`Dirac1933`, `Feynman1948`, `Connes1994`, `Landsman1998`) and add independent anchors for the 1D `U(2)` contact-interaction classification mentioned in the RG-fundamental draft.
98. [done] Execute AN-32L Lean support lane: formalized weighted-local truncation, graph-decay finite-channel operator bounds, and denominator-rate ratio bookkeeping in `research/workspace/proofs/Claim1lean/WeightedLocalGraphDecay.lean` (see `research/workspace/notes/theorems/2026-02-10-claim1-lean-weighted-local-graph-decay-bridge.md`).
99. [done] Execute AN-33A draft lane: added theorem skeleton + Lean-obligation map in `research/workspace/notes/theorems/2026-02-10-claim1-d3-an33-graph-decay-nonlocal-weighted-local.md`.
100. [done] Execute AN-33B closure lane: discharged AN-33A graph-decay and denominator-rate hypotheses in the scoped branch and completed theorem-grade nonlocal weighted-local lift in `research/workspace/notes/theorems/2026-02-10-claim1-d3-an33b-graph-decay-denominator-closure.md`, with diagnostics `research/workspace/simulations/claim1_d3_an33_graph_decay_nonlocal_weighted_local_check.py`.
101. [done] Execute AN-34A: replaced AN-33 denominator-rate assumptions with first-principles shell-tail in-branch estimates and tightened ratio-rate interfaces in `research/workspace/notes/theorems/2026-02-10-claim1-d3-an34-firstprinciples-tail-rate-transmutation.md`, with diagnostics `research/workspace/simulations/claim1_d3_an34_firstprinciples_tail_rate_check.py`.
102. [next] Execute AN-33L/AN-34L continuation: lift weighted-local graph-decay and tail-to-rate finite lemmas to exhaustion-indexed projective-family bookkeeping for the same scoped branch.

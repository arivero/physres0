# Core Goal Compass (Foundational Track)

Date: 2026-02-09

Terminology companion:

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
- `theorems/2026-02-10-claim1-d3-an33l-an34l-exhaustion-transfer-lean-bridge.md`
- `theorems/2026-02-10-claim1-d3-an33l-b-projective-dereg-transfer-lean.md`
- `theorems/2026-02-10-claim1-d3-an33l-c-commuting-limit-wrapper-lean.md`
- `theorems/2026-02-10-claim1-lean-semigroup-generator-lemma.md`
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

## North Star

Understand, rigorously, how quantum formalism appears when variational mechanics is made distributionally consistent across:

1. static problems,
2. mechanics on time-lines,
3. field theory on spacetime,

and connect that emergence to geometric descriptions of forces.

## Long Thinking Question (Newton Limit Paradox)

What is the precise mathematical paradox/inconsistency that makes the naive
"Newton-only" limit unrigorous and forces quantum structure (amplitudes /
half-densities / phases) to restore consistency, in analogy with how calculus
resolves Zeno-style limit paradoxes?

Working note: `research/workspace/notes/2026-02-10-newton-limit-paradox-quantum-necessity.md`.

## Canonical Source Anchors (`conv_patched.md`)

- Variational/distribution seed: `conv_patched.md:681`, `conv_patched.md:684`, `conv_patched.md:733`, `conv_patched.md:1085`.
- Halved/amplitude-to-density interpretation: `conv_patched.md:710`, `conv_patched.md:932`, `conv_patched.md:1195`.
- Scale/refinement/RG/tangent-groupoid control: `conv_patched.md:795`, `conv_patched.md:799`, `conv_patched.md:1118`, `conv_patched.md:1207`.
- Action -> force/geodesic/gauge bridge: `conv_patched.md:549`, `conv_patched.md:595`, `conv_patched.md:601`, `conv_patched.md:611`.

## Immediate Execution Priorities

1. **Goal 1A (highest priority):** close a proof of consistency for statics and package it as a paper on probability amplitudes (with geometric \(1/2\)-density appendix language), with explicit equivalence statement to quantum mechanics without time evolution.
2. **Goal 1B (immediate next):** close consistency for dynamics on time histories and package it as a second paper establishing equivalence to the path-integral formalism, including a dedicated historical discussion section.
3. Keep Goal 1 explicitly three-level (statics \(\to\) dynamics \(\to\) fields); continue the field dimension ladder (\(d=2\to d=3\to d=4\) frontier) as a downstream extension after Goal 1A and Goal 1B manuscript locks.
4. Use Lean-first verification for reusable lemmas (\(c\)-invariance, small-\(\kappa\) control, covariance bounds), with symbolic/numeric checks as complements to paper-facing theorem chains.

## Progress (This Pass)

- Priority 1 completed (Phase AG): \(\eta\to0^+\) de-regularization note for finite-\(g\) multi-mode quartic sector.
- Priority 2 completed (Phase AH): unified action-reduction synthesis note across SR/GR/gauge.
- Follow-up completed (Phase AI): consolidated lecture manuscript "Newton -> action -> path integral" with explicit dependency graph.
- Priority 3 completed (Phase AJ): tangent-groupoid/\(\tau_\mu\)/Schwinger-Dyson dependency sheet.
- Integration completed (Phase AK): \(c\)-invariance dependency logic wired into the scoped Claim 1 manuscript.
- Frontier step completed (Phase AL): first explicit continuum-limit theorem candidate using the \(c\)-invariance backbone.
- New structure lock completed (Phase AM): Goal 1 reorganized as a three-level program with explicit field-level dimension-dependent existence ladder.
- Field execution map completed (Phase AN): dimension-gated field existence roadmap with concrete next deliverables (AN-1/AN-2/AN-3).
- Field bridge draft completed (Phase AO): first \(d=2\) field-indexed Claim 1 candidate with explicit \(d=4\) obstruction checklist.
- Field theorem closure completed (Phase AP): closed \(d=2\) interacting ultralocal \(\phi^4\) field-level Claim 1 theorem (existence + SD + \(c\)-invariance).
- Lift-gap analysis completed (Phase AQ): explicit \(d=4\) obstruction sheet mapping why AP does not auto-lift once local propagation is restored.
- Formal split completed (Phase AR): geometric \(1/2\)-density claims separated into kinematic algebraic truths vs dynamical continuum-existence gates.
- Intermediate rung drafted (Phase AS): \(d=3\) beyond-ultralocal bridge candidate with explicit closure obligations B1-B5.
- Quantitative bridge step completed (Phase AT): proved a small-\(\kappa\) Lipschitz prototype estimate (B5 surrogate) for a nearest-neighbor finite-dimensional model.
- Formal verification ramp completed (Phase AU): Lean workspace with mathlib integrated; \(c\)-invariance and small-\(\kappa\) Lipschitz core lemmas are machine-checked.
- Lean bridge extension completed (Phase AV): quotient-derivative covariance-form lemma formalized in Lean for the AN-5 derivative-control backbone.
- Lean inequality bridge completed (Phase AW): finite-support covariance-style centered-product bound formalized in Lean.
- Lean derivative template completed (Phase AX): AN-7 + AN-8 combined into a machine-checked abstract `|∂ω|` bound for ratio states.
- Lean interval bridge completed (Phase AY): machine-checked interval increment bound from derivative templates, including centered-average AN-9 instantiation.
- Lean assumption-reduction completed (Phase AZ): interior `derivWithin = deriv` bridge and boundary-aware ratio increment template formalized.
- Lean one-sided boundary reduction completed (Phase BA): \(t=0\) `Icc`↔`Ici` derivative bridge and one-sided boundary variant of centered-average increment bound.
- Lean dependency map completed (Phase BB): module-level spine from AU→BA to B5 obligations with explicit next missing formal ingredient.
- Lean finite-model derivative bridge completed (Phase BC): finite exponential-family parameter-derivative lemmas machine-checked (`N'=-A`, `Z'=-B`) to discharge AN-7 derivative hypotheses in a concrete scoped class.
- Lean finite-model representation bridge completed (Phase BD): centered covariance representation for the finite exponential-family ratio state machine-checked in weighted and normalized-weight forms.
- Lean finite-model derivative bound completed (Phase BE): model-internal \(|\omega'|\) bounds machine-checked from BD representation without external representation hypotheses.
- Lean finite-model increment bound completed (Phase BF): AN-10-style interval `Cκ` theorem machine-checked for the finite exponential family under explicit uniform interval assumptions.
- Lean automatic-regularity closure completed (Phase BG1 / AN-18): finite-model `Zsum>0`, `Zsum≠0`, global differentiability, and interval `derivWithin=deriv` bridge formalized and wired into an AN-18 auto-wrapper theorem reducing BF regularity assumptions to centered/moment controls.
- Priority reset recorded (Phase BG0): Goal 1 ordering updated to statics-consistency paper first, then dynamics/path-integral-equivalence paper with historical framing.
- \(d=3\) bridge alignment update completed (Phase BG2 / AN-19): AN-18 finite-model assumption collapse is now mapped into B5 structure in the \(d=3\) bridge candidate, separating resolved regularity bookkeeping from remaining field-side centered/moment obligations.
- Goal 1C paper kickoff completed (Phase BK): field-theory general-dimension manuscript track started with explicit G1/G2/G3 closure gates and literature anchors (`2026-02-09-claim1-paper3-field-theory-general-dimension-roadmap.{md,tex}`).
- \(d=3\) finite-volume B5b constants completed (Phase BL / AN-20): explicit centered/moment proposition added with uniform finite-volume constants and synced into Paper 3 + bridge note.
- \(d=3\) renormalized B5b channel completed (Phase BM / AN-21): AN-20 raw \(a^{-3}\) moment scaling replaced by an \(a\)-uniform renormalized channel with explicit finite-volume constants, synced into Paper 3 + bridge note.
- \(d=3\) scoped continuum-branch candidate completed (Phase BN / AN-22): AN-21 renormalized B5b input integrated with B1-B4 into an explicit scoped continuum theorem candidate, synced into Paper 3 + bridge note.
- \(d=3\) concrete B1-B4 closure completed (Phase BO / AN-23): compact-spin interacting Euclidean subclass closes B1-B4 (tightness, \(Z>0\), SD pass-through) and upgrades the AN-22 candidate to scoped closure in that subclass.
- \(d=3\) hard-cutoff lift completed (Phase BP / AN-24): removed \(R\to\infty\) artifact in the AN-23 branch with B1-B4 preserved in the Euclidean local-renormalized channel.
- \(d=3\) class-extension lane completed (Phase BQ / AN-25): observable-side compact-support \(\to\) bounded-continuous local extension is closed and synchronized with SD test-side closure.
- \(d=3\) SD test-side tail insertion closure completed (Phase BR / AN-26): \(C_c^1\to C_b^1\) extension is closed in-branch.
- \(d=3\) insertion-moment gate verification completed (Phase BS / AN-26B): explicit uniform insertion \(L^{4/3}\)-moment bound discharges AN-26 hypotheses in the scoped Euclidean branch.
- \(d=3\) oscillatory/de-regularized class transfer completed (Phase BT / AN-27): widened local classes and SD-test extension now pass to \(c_\eta=\eta-i/h\) and \(\eta\to0^+\) in the scoped branch under explicit non-vanishing/envelope hypotheses.
- \(d=3\) first nonlocal-cylinder transfer completed (Phase BU / AN-28): disconnected two-block bounded cylinders and \(C_b^1\) SD-test extension now persist in the same oscillatory/de-regularized branch under explicit denominator/moment assumptions.
- \(d=3\) nonlocal refinement-Cauchy closure completed (Phase BV / AN-29): explicit numerator/denominator scale-rate bookkeeping now yields refinement Cauchy bounds and SD pass-through for AN-28 nonlocal cylinders in the same scoped branch.
- \(d=3\) multiblock projective-consistency closure completed (Phase BW / AN-30): finite graph-indexed nonlocal families now carry explicit combinatorial Cauchy constants and projective-consistent refinement limits.
- \(d=3\) exhaustion-summability lift completed (Phase BX / AN-31): AN-30 now extends to uniformly locally finite exhaustion families with explicit tail-summability Cauchy/projective control.
- \(d=3\) weighted-local SD-test lift completed (Phase BY / AN-32): AN-31 now extends from cylinder classes to weighted-local observable/SD-test classes with explicit exhaustion-uniform insertion tail estimates, synchronized into Paper 3 and diagnostics script (`claim1_d3_an32_weighted_local_sdtest_check.py`).
- \(d=3\) graph-decay nonlocal weighted-local closure completed (Phase BZ / AN-33): AN-32 now extends to graph-decay nonlocal weighted-local channels with explicit denominator-rate normalized bookkeeping and SD pass-through closure in the same scoped branch, synchronized with diagnostics script (`claim1_d3_an33_graph_decay_nonlocal_weighted_local_check.py`).
- \(d=3\) first-principles tail-rate transmutation completed (Phase CA / AN-34A): AN-33 denominator/numerator rate assumptions are replaced by explicit shell-tail-derived bounds with Lean support wrappers and diagnostics script (`claim1_d3_an34_firstprinciples_tail_rate_check.py`).
- \(d=3\) exhaustion-level Lean transfer bridge completed (Phase CB / AN-33L/AN-34L-A): one-sided tail envelopes now map to AN-31-style pairwise Cauchy/projective-rate bookkeeping via machine-checked wrappers in `Claim1lean/WeightedLocalGraphDecay.lean`.
- \(d=3\) projective-defect/de-regularization Lean transfer completed (Phase CC / AN-33L-B): AN-31/AN-34 field-side transfer now has machine-checked mismatch-penalty wrappers for projective defects and pairwise exhaustion rates.
- \(d=3\) commuting-limit wrapper completed (Phase CD / AN-33L-C): exhaustion tail envelopes plus regularization proxy Cauchy envelopes are packaged into a single joint convergence lemma in Lean (`commuting_limit_of_exhaustion_and_regularization_envelopes`).

## Next Active Target

- Phase BH (completed): Goal 1A paper lock delivered (`2026-02-09-claim1-paper1-static-amplitude-qm-equivalence.{md,tex,pdf}`).
- Phase BI (completed): Goal 1B paper lock delivered (`2026-02-09-claim1-paper2-dynamics-path-integral-equivalence-history.{md,tex,pdf}`).
- Phase BJ (paper-sync gate, done for AN-18): AN-18 assumption updates were propagated to both paper manuscripts in the same execution pass.
- Phase BK (completed): Goal 1C paper track draft started (`2026-02-09-claim1-paper3-field-theory-general-dimension-roadmap.{md,tex}`).
- Phase BL (completed): AN-20 finite-volume centered/moment proposition delivered and integrated into Goal 1C track.
- Phase BM (completed): AN-21 renormalized B5b channel delivered and integrated into Goal 1C track.
- Phase BN (completed): AN-22 scoped continuum-branch theorem candidate delivered and integrated into Goal 1C track.
- Phase BO (completed): AN-23 compact-spin \(d=3\) B1-B4 closure delivered and integrated into the bridge lane.
- Phase BP (completed): AN-24 hard-cutoff lift \(R\to\infty\) delivered in the AN-23 branch.
- Phase BQ (completed): AN-25 local class-extension lane completed in the scoped Euclidean branch.
- Phase BR (completed): AN-26 SD-test tail-control theorem delivered.
- Phase BS (completed): AN-26B insertion-moment verification delivered.
- Phase BT (completed): AN-27 oscillatory/de-regularized class-transfer note delivered.
- Phase BU (completed): AN-28 first nonlocal-cylinder transfer note delivered.
- Phase BV (completed): AN-29 refinement-Cauchy nonlocal-cylinder continuum extraction delivered.
- Phase BW (completed): AN-30 finite graph-indexed multiblock/projective-consistency closure delivered.
- Phase BX (completed): AN-31 exhaustion-family summability lift delivered.
- Phase BY (completed): AN-32 weighted-local SD-test lift delivered.
- Phase BZ (completed): AN-33 graph-decay nonlocal weighted-local closure delivered.
- Phase CA (completed): AN-34A first-principles tail-rate transmutation delivered.
- Phase CB (completed): AN-33L/AN-34L-A exhaustion-level Lean transfer wrappers delivered.
- Phase CC (completed): AN-33L-B projective-defect/de-regularization transfer lemmas delivered.
- Phase CD (completed): AN-33L-C commuting-limit wrapper delivered.
- Active support lane: semigroup→generator lemma is now Lean-checked (`Claim1lean/SemigroupGenerator.lean`); next formalize semigroup/normalization theorems (Gaussian `t^{-d/2}` and Van Vleck-style prefactors) supporting the Newton-limit paradox framing and tighten reconstruction-facing interfaces.

### Paper Synchronization Trigger (Future Chain Rule)

After any new theorem/Lean result, update the relevant Goal 1 paper track(s) (Paper 1, Paper 2, Paper 3) in the same pass if any of the following is true:

1. hypothesis set changes (added/removed/relaxed assumptions),
2. theorem strength changes (candidate -> proved, scoped -> wider scope, or new limitation),
3. confidence label changes (`proved/heuristic/speculative` score movement),
4. terminology rule changes affecting statement wording,
5. new reproducibility artifact (script/proof module) becomes citation-relevant.

## Terminology Guardrail

Apply the skepticism protocol in `2026-02-09-wikipedia-baseline-definitions-and-skepticism.md`:

1. use Wikipedia for baseline orientation only,
2. require technical-source cross-check before promoting terminology-critical claims,
3. mark terminology as provisional whenever definition and proof scope are misaligned.

## De-Prioritized Unless Supporting North Star

- Additional rotating-black-hole taxonomy refinements.
- Additional phase-taxonomy refinements for gauge long-range classes.

These are kept secondary unless they directly improve the foundational thread above.

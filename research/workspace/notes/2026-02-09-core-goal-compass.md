# Core Goal Compass (Foundational Track)

Date: 2026-02-09

Terminology companion:

- `2026-02-09-foundational-glossary.md`
- `theorems/2026-02-09-claim1-three-level-program.md`
- `theorems/2026-02-09-claim1-field-dimension-existence-roadmap.md`
- `theorems/2026-02-09-claim1-d2-field-cylinder-candidate.md`
- `theorems/2026-02-09-claim1-d2-ultralocal-phi4-closure.md`
- `theorems/2026-02-09-claim1-d4-lift-obstruction-sheet.md`
- `theorems/2026-02-09-claim1-halfdensity-kinematic-dynamic-split.md`
- `theorems/2026-02-09-claim1-d3-intermediate-bridge-candidate.md`
- `theorems/2026-02-09-claim1-d3-small-kappa-lipschitz-prototype.md`
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

## North Star

Understand, rigorously, how quantum formalism appears when variational mechanics is made distributionally consistent across:

1. static problems,
2. mechanics on time-lines,
3. field theory on spacetime,

and connect that emergence to geometric descriptions of forces.

## Canonical Source Anchors (`conv_patched.md`)

- Variational/distribution seed: `conv_patched.md:681`, `conv_patched.md:684`, `conv_patched.md:733`, `conv_patched.md:1085`.
- Halved/amplitude-half-density interpretation: `conv_patched.md:710`, `conv_patched.md:932`, `conv_patched.md:1195`.
- Scale/refinement/RG/tangent-groupoid control: `conv_patched.md:795`, `conv_patched.md:799`, `conv_patched.md:1118`, `conv_patched.md:1207`.
- Action -> force/geodesic/gauge bridge: `conv_patched.md:549`, `conv_patched.md:595`, `conv_patched.md:601`, `conv_patched.md:611`.

## Immediate Execution Priorities

1. Keep Goal 1 explicitly three-level: statics \(\to\) dynamics \(\to\) fields, with half-density optional at each level and assumptions stated branchwise.
2. For field level, enforce a dimension-indexed existence program (\(d=2\), then \(d=3\), then \(d=4\) frontier) instead of a dimension-blind continuum claim.
3. Promote the Claim 1 continuum candidate to a closed non-Gaussian theorem in one field-compatible class, with explicit statement of why the same proof does or does not lift to \(d=4\).
4. Use Lean-first verification for core reusable lemmas (\(c\)-invariance, small-\(\kappa\) control, covariance bounds), keeping numerical checks as complement.

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
- Formal split completed (Phase AR): half-density claims separated into kinematic algebraic truths vs dynamical continuum-existence gates.
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

## Next Active Target

- Phase BE (AN-16): formalize a finite exponential-family derivative-bound corollary (from BD representation plus inequality templates) that feeds AN-10 increment control with minimal extra assumptions.

## De-Prioritized Unless Supporting North Star

- Additional rotating-black-hole taxonomy refinements.
- Additional phase-taxonomy refinements for gauge long-range classes.

These are kept secondary unless they directly improve the foundational thread above.

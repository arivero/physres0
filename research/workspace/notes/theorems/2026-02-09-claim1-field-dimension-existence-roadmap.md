# Claim 1 Phase AN: Field-Level Existence Roadmap by Spacetime Dimension

Date: 2026-02-09 (CET)  
Depends on: `research/workspace/notes/theorems/2026-02-09-claim1-three-level-program.md`

## Purpose

Turn the field-level part of Goal 1 into a dimension-gated proof program.

Terminology guardrail:
default to probability/transition amplitude wording; use geometric \(1/2\)-density terminology only when the object is explicitly a square-root density-bundle kernel.

## Existence Notions (Field Level)

For each spacetime dimension \(d\), distinguish:

1. **Regulated existence**: finite cutoff/lattice and finite volume objects are well-defined.
2. **Continuum existence**: removal of regulator/volume with nontrivial limit.
3. **Physical reconstruction**: Euclidean-to-Minkowski reconstruction (or equivalent axiomatic bridge) in the model class.

Claim 1 only upgrades to field-level closure in a branch when all three are addressed in that branch.

## Dimension Gate

### \(d=2\) (first closure target)

Program stance:

1. treat \(d=2\) interacting scalar classes as the primary candidate for first full field-level closure;
2. prove Claim 1-style localization/SD/\(c\)-invariance statements inside a model where continuum existence is strongest.

Amplitude / geometric \(1/2\)-density branching:

1. probability-amplitude language is primary; geometric \(1/2\)-density language can be used as structural interpretation,
2. correlator/Schwinger-function branch can carry the strict existence proof.

### \(d=3\) (second closure target)

Program stance:

1. move next to superrenormalizable interacting classes in \(d=3\),
2. document every added renormalization assumption versus \(d=2\).

Amplitude / geometric \(1/2\)-density branching:

1. keep geometric \(1/2\)-density interpretation optional,
2. prioritize robust continuum/correlation control first.

### \(d=4\) (frontier target)

Program stance:

1. treat \(d=4\) as physically central and mathematically frontier-sensitive,
2. split results into:
   - theorem-grade scoped statements,
   - explicit open hypotheses needed for full continuum nontriviality.

Amplitude / geometric \(1/2\)-density branching:

1. admissible as formal/compositional language,
2. not accepted as substitute for continuum existence proof.

### \(d>4\) (EFT branch)

Program stance:

1. default to EFT/scaling analysis unless a specific UV-complete model is fixed,
2. keep out of the near-term closure queue.

## Immediate Claim 1 Deliverables (Current State)

1. **AN-1 (done):** \(d=2\) field-indexed cylinder candidate drafted and then closed in an explicit ultralocal interacting class.
2. **AN-2 (done):** \(d=4\) lift-obstruction sheet completed (power-count and locality-restoration failure modes explicit).
3. **AN-3 (done):** geometric \(1/2\)-density kinematic/dynamical split formalized.
4. **AN-4/AN-5 (done):** \(d=3\) intermediate bridge candidate plus quantitative small-\(\kappa\) B5-prototype control.
5. **AN-6\(\rightarrow\)AN-18 (done, Lean support lane):** finite-model machine-checked chain completed through auto-regularity reduction of BF assumptions.
6. **AN-19 (done):** translated the AN-18 Lean assumption collapse into the \(d=3\) bridge obligations (B5 split into resolved regularity bookkeeping vs remaining centered/moment field obligations).
7. **AN-20 (done):** first \(d=3\) finite-volume centered/moment proposition delivered with explicit constants (`research/workspace/notes/theorems/2026-02-09-claim1-d3-finite-volume-centered-moment-proposition.md`), feeding the AN-19 B5b lane.
8. **AN-21 (done):** replaced AN-20's explicit finite-volume \(a^{-3}\) moment channel with an \(a\)-uniform renormalized bound channel in `research/workspace/notes/theorems/2026-02-09-claim1-d3-renormalized-moment-channel-proposition.md`.
9. **AN-22 (done):** combined AN-21 renormalized B5b input with B1-B4 as a scoped \(d=3\) continuum-branch theorem candidate in `research/workspace/notes/theorems/2026-02-09-claim1-d3-scoped-continuum-branch-candidate.md`.
10. **AN-23 (done):** discharged B1-B4 in an explicit interacting compact-spin \(d=3\) subclass (tightness + denominator non-vanishing + SD insertion pass-through) in `research/workspace/notes/theorems/2026-02-09-claim1-d3-compact-spin-b1-b4-closure.md`.
11. **Goal 1C paper track (done):** started a general-dimension field manuscript with explicit closure gates and literature anchors (`research/workspace/reports/2026-02-09-claim1-paper3-field-theory-general-dimension-roadmap.tex`).
12. **AN-24 (done):** removed hard cutoff \(R\to\infty\) in the AN-23 Euclidean branch while preserving B1-B4 in the local-renormalized channel (`research/workspace/notes/theorems/2026-02-09-claim1-d3-cutoff-lift-closure.md`).
13. **AN-25 (active):** started AN-24 class extension in `research/workspace/notes/theorems/2026-02-09-claim1-d3-class-extension-local-cb-channel.md`; observable-side \(C_c\to C_b\) extension is closed, while full SD test-side \(C_b^1\) extension is still open.
14. **AN-26 (next):** complete AN-25 by discharging tail insertion-control for \(C_b^1\) SD tests, then begin oscillatory/de-regularized transfer in the same \(d=3\) branch.

## Non-Drift Rule

Any new field-level theorem note must start with:

1. target dimension \(d\),
2. model class,
3. existence notion being claimed (regulated / continuum / reconstruction),
4. whether geometric \(1/2\)-density language is used as core formalism or as interpretation only.

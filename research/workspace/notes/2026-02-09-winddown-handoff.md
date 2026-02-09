# Wind-Down Handoff: Markdown Corpus Scan and Proof Frontier

Date: 2026-02-09 (US)

## Scope of this pass

Corpus scanned:

1. all tracked Markdown files in repo (`102` files from `rg --files -g '*.md'`),
2. status-bearing notes and reports in `research/workspace/notes/` and `research/workspace/reports/`,
3. audit backbone in `research/workspace/notes/audits/2026-02-08-top10-claim-audit.md`.

This note records what is learned and what remains to be proved, then leaves a
clear next-agent queue.

## What we have learned (stable across the scanned md corpus)

1. Goal 1A is manuscript-locked at scoped theorem grade:
   static variational consistency and static QM measurement-layer equivalence
   (`research/workspace/reports/2026-02-09-claim1-paper1-static-amplitude-qm-equivalence.md`).
2. Goal 1B is manuscript-locked at scoped theorem grade:
   dynamic consistency and scoped path-integral equivalence with historical
   section (`research/workspace/reports/2026-02-09-claim1-paper2-dynamics-path-integral-equivalence-history.md`).
3. Goal 1C field program is advanced to AN-31 in a scoped \(d=3\) lane:
   hard-cutoff lift, class extension, oscillatory/de-regularized transfer,
   nonlocal cylinder continuum Cauchy control, finite graph multiblock closure,
   and exhaustion-summability lift
   (`research/workspace/reports/2026-02-09-claim1-paper3-field-theory-general-dimension-roadmap.md`).
4. Top-10 audit snapshot currently encodes:
   Claims 2, 3, 4, 5, 6, 7, 10 as proved in scoped models;
   Claim 8 at open-sector heuristic closure;
   Claim 9 with screened-Abelian theorem closure plus scoped non-Abelian lanes;
   Claim 1 high score with scoped closure and explicit remaining global gap
   (`research/workspace/notes/audits/2026-02-08-top10-claim-audit.md`).
5. Claim 9 non-Abelian transfer ladder is staged AC -> AD -> AE, and this pass
   adds AF draft lane:
   `research/workspace/notes/theorems/2026-02-09-claim9-nonabelian-firstprinciples-transfer-clustering.md`.

## What is still to be proved (frontier items)

1. Claim 1 frontier:
   AN-32 remains next in queue (weighted-local SD-test class extension with
   exhaustion-uniform insertion bounds), and full \(d=4\) interacting G2/G3
   closure remains open.
2. Claim 9 frontier:
   first-principles beyond-window transfer control must be fully integrated and
   validated across manuscript/audit (AF lane is drafted but not yet fully
   propagated), and dynamical-matter string-breaking remains program-level.
3. Claim 8 frontier:
   unresolved \(D\ge 6\) multi-spin rotating sectors remain explicitly open.
4. Global frontier:
   full continuum interacting equivalence claims remain outside current scoped
   theorem envelope.

## Immediate handoff queue for the next agent

1. Claim 9 AF integration:
   sync AF lane into Claim 9 paper and audit score rationale only after script
   and bound checks are passing in the same pass.
2. Claim 9 matter lane:
   start a theorem-grade string-breaking crossover sheet with explicit
   \((G,D,N_f)\)-tagged assumptions and extraction window.
3. Claim 1 AN-32:
   extend AN-31 from cylinder observables to weighted-local SD-test classes,
   then trigger Paper 3 synchronization in the same pass.
4. Paper synchronization rule:
   keep the trigger policy from
   `research/workspace/notes/2026-02-09-core-goal-compass.md`
   active whenever theorem assumptions, confidence labels, or reproducibility
   artifacts change.

## Skepticism and terminology guardrail reminder

1. Use Wikipedia only for baseline orientation.
2. Promote theorem-critical terminology only after technical-source
   cross-check.
3. Mark terminology as provisional if proof scope and term usage diverge.
4. Keep raw DOI/arXiv downloads in `research/.ignore/downloads/`.

## Validation contract for this handoff note

### Assumptions

1. this note is a status synthesis, not a new theorem proof,
2. status labels are read from current md corpus and audit artifacts.

### Units and dimensions check

1. no new physical quantity is introduced; units are inherited from cited notes.

### Symmetry/conservation checks

1. no new dynamical or symmetry claim is introduced in this handoff itself.

### Independent cross-check path

Run:

```bash
rg --files -g '*.md' | wc -l
rg -n -g '*.md' '\b(done|closed|proved|theorem-grade|queued|next|open gap|remaining gap|frontier|candidate|heuristic|speculative)\b' research/workspace
```

### Confidence statement

High confidence for the status extraction; medium confidence for frontier
prioritization ordering (depends on next scientific objective weighting).

### Reproducibility metadata

1. shell: `zsh`,
2. date anchor: 2026-02-09 (US),
3. command log basis:
   `rg --files -g '*.md'`,
   `rg -n -g '*.md' ...`,
   targeted `sed` reads of paper and audit md files.

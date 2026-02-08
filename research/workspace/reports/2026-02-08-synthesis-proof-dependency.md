# Synthesis Report: Proof Dependencies and Long-Horizon Program

Date: 2026-02-08  
Primary source of claims: `conv_patched.md`  
Current status index: `research/workspace/notes/audits/2026-02-08-top10-claim-audit.md`

## 1. Status Snapshot

1. `proved`: Claims 2, 4, 5, 6, 7, 10.
2. `heuristic`: Claims 3, 8, 9.
3. `speculative`: Claim 1.

Interpretation:

1. Classical/SR/GR force-orbit structure is now mostly theorem-grade in scoped models.
2. The remaining frontier is quantization bridge rigor (Claim 1) plus model-class closure in high-D/rotating gravity and gauge sectors.

## 2. Dependency Graph

```text
Claim 10 (SR circular thresholds n=2,3)
  -> supports sanity checks for Claims 2,3,4

Claim 2 (center-access trichotomy)
  -> supports global intuition used in Claims 3,4

Claim 3 (SR Coulomb classification, global-time partial)
  -> supports relativistic inverse-square benchmark branch

Claim 4 (n=3 Duffing + global-time topology)
  -> closes inverse-cubic non-generic boundedness picture

Claim 5 (D-dim GR matching)
  -> feeds Claims 6,7,8 dimensional interpretation

Claim 6 (Schwarzschild fixed-E interval)
  + Claim 7 (ISCO threshold)
  -> strong 4D GR bounded-orbit backbone

Claim 8 (high-D stability: Tangherlini + asymptotic extension)
  -> pending rotating/global class closure

Claim 9 (phase/model-class split gauge long-range taxonomy)
  -> pending theorem-grade closure per model framework

Claim 1 (half-density/groupoid/path-integral bridge)
  currently layered as:
    static theorem core
    finite-N variational-delta lemmas
    finite-dimensional manifold half-density convolution
    point-supported scaling-channel decomposition
    cylinder-limit program with failure modes
  -> pending continuum renormalized equivalence theorem
```

## 3. Long-Horizon Conjecture List

### C1: Renormalized Cylinder-Limit Existence (QM/QFT)

There exists a renormalization scheme such that normalized cylinder observables converge to a continuum functional compatible with Claim 1 channel decomposition.

### C2: Channel-Stable Continuum Map

Point-supported scaling channels (\(\delta^{(m)}\)-type modes) admit a controlled flow under continuum limit with explicit mixing matrix / selection rules.

### C3: Groupoid-to-Propagator Equivalence

A theorem-level equivalence can be established between an admissible tangent-groupoid half-density family and the corresponding continuum propagator class for specified model spaces.

### C4: Rotating High-D Orbit Stability Closure

A complete parameterized theorem map exists for stable timelike circular/bound geodesics across rotating high-D black-hole families under explicit assumptions.

### C5: Gauge Model-Class Theorem Closure

For each model class (pure YM, YM+fundamental matter, Abelian Higgs), asymptotic \(V(r)\) claims can be upgraded from proposition-level to theorem-level under chosen framework assumptions.

## 4. Work Packages (A Long Program)

### WP-1 (Claim 1 Core Continuum)

1. Formalize cylinder-limit topology and observable class.
2. Prove convergence for Gaussian/semi-Gaussian reference families.
3. Add counterterm flow and channel-tracking lemmas.

Deliverable: `claim1-continuum-skeleton.md` + reproducible toy proofs.

### WP-2 (Claim 1 Geometric Algebra)

1. Strengthen tangent-groupoid theorem pack to full statement with explicit symbol classes.
2. Add composition continuity at \(\varepsilon=0\) in theorem format.

Deliverable: theorem-grade groupoid-convolution continuity note.

### WP-3 (Claim 3/8/9 Closure)

1. Claim 3: collision/escape asymptotic-time estimates.
2. Claim 8: rotating-class theorem map.
3. Claim 9: framework-specific theorem closure (lattice/continuum assumptions).

Deliverable: status upgrades from `heuristic` where closure is achieved.

### WP-4 (Unified Manuscript)

1. Compile integrated manuscript from theorem notes.
2. Attach dependency graph and conjecture index.
3. Include script/test appendix as reproducibility backbone.

Deliverable: long-form report ready for iterative review.

## 5. Immediate Next Execution Target

Start WP-1 with a strict continuum skeleton note:

`research/workspace/notes/theorems/2026-02-08-claim1-continuum-skeleton.md`

including:

1. exact spaces/topologies,
2. normalization/counterterm map,
3. convergence statement template,
4. failure-mode diagnostics tied to existing toy scripts.

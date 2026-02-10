# Physarticle Narrative Read: Ideas + Rigorization Hooks

Date: 2026-02-10 (US)

## Scope

Read the `../physarticle` *Markdown* “article” sources (narrative format) to extract extra ideas/hypotheses/hooks beyond the TeX proposition list.

Primary sources read:

- `../physarticle/paper/main.md`
- `../physarticle/papers/delta-objects/main.md`
- `../physarticle/papers/half-density-qft/main.md`
- `../physarticle/papers/planck-area/main.md`
- `../physarticle/papers/rg-fundamental/main.md`
- `../physarticle/paper/notes/half-density-kernel-normalization.md`
- `../physarticle/paper/notes/van-vleck-schur-complement.md`
- `../physarticle/paper/notes/rivero-ode-0302285-simple.md`

This note is *idea extraction / task seeding*, not a proof pass.

## High-value idea extracts (with “how to make it rigorous” hooks)

### 1) “Square-root Jacobian” as the unifying exponent across contexts

Appears as:

1. identity delta kernel scaling near the diagonal (`delta-objects/main.md`, §2),
2. forced `t^{-d/2}` short-time normalization from semigroup composition (`paper/notes/half-density-kernel-normalization.md`),
3. stationary phase amplitude weights `|det Hess|^{-1/2}` squaring to density weights in `δ(∇f)` (`delta-objects/main.md`, §3.3),
4. Van Vleck / mixed Hessian determinants after eliminating intermediate variables (Schur complement template; `paper/notes/van-vleck-schur-complement.md`).

Rigorization hooks:

- package as a *finite-dimensional* theorem chain:
  - exact Gaussian convolution semigroup ⇒ exponent `d/2`,
  - Gaussian elimination ⇒ Schur complement + determinant prefactor,
  - stationary phase lemma ⇒ amplitude half-determinant vs density determinant.
- then map to the existing Claim 1 “half-density kinematic vs dynamical” split: kinematics explains exponents; dynamics is the continuum-limit gate.

### 2) “Delta objects” dictionary: `δ(f')` vs `δ'` vs point interactions

Key dictionary items (all finite-dimensional / distributional):

- `δ(f')` localizes to stationary points with `1/|f''|` weights (and multivariate `δ(∇f)` with `1/|det Hess|`).
- `δ'` is a distributional derivative probing test-function derivatives; realized by point-splitting:
  `(δ(·+ε)−δ)/ε → δ'`.
- point interactions as rank-one kernels `g|0⟩⟨0|` are cleanly written as bi-half-density distributions supported at `(0,0)`.

Rigorization hooks:

- formalize the point-splitting limit and sign conventions once (one-page lemma),
- use the half-density kernel calculus to keep “derivative moves between slots” as a coordinate-free Lie-derivative identity (see item 4 below).

### 3) “RG is definitional” via the derivative micro-model + scheme fixing

The narrative emphasizes the pattern:

`regulate → subtract divergence → fix finite ambiguity by normalization → take limit`,

with the derivative as the toy prototype (difference quotient; plus optional finite subtraction `z0` fixed by `D(1)=0`).

Rigorization hooks:

- make this a precise “renormalized operator” template (functional-analytic statement),
- then use it as a *didactic bridge* to QFT/QM RG examples (2D delta is the worked model).

### 4) Locality/contact terms as diagonal delta-kernel statements (QFT note)

The QFT half-density note frames counterterms/contact terms as distributions supported on the diagonal `x=y`, naturally expressed using the canonical bi-half-density delta kernel.

Also: a coordinate-free identity for shifting derivatives between kernel slots:

`(ℒ_{V_x}+ℒ_{V_y}) K_Id = 0  ⇒  ℒ_{V_x}K_Id = −ℒ_{V_y}K_Id`.

Rigorization hooks:

- prove the Lie-derivative identity for the identity kernel in the half-density bundle setting;
- then treat “contact terms = diagonal distributions” as a clean semantic layer for SD/IBP identities (ties into the Claim 1 SD pipeline).

### 5) Densitized scalar fields: `ψ = |g|^{1/4} φ` and conjugated kinetic operator

The QFT note highlights:

- treating fields as half-densities makes kernels canonical without choosing a background measure;
- conjugation `P ↦ |g|^{1/4} P |g|^{-1/4}` gives a symmetric operator in the coordinate pairing.
- a recorded conformal-class expansion shows a coefficient proportional to `D(4−D)` cancels at `D=4` (flagged as “maybe meaningful, maybe just an algebraic simplification”).

Rigorization hooks:

- write as a clean lemma about unitary equivalence between `L^2(M, √|g| dx)` scalar fields and `L^2` half-densities;
- optionally check the conformal expansion with an independent symbolic script before interpreting it.

### 6) Planck-area “dimension sieve” is a hypothesis ladder, not a theorem (yet)

The planck-area draft cleanly separates:

- forced facts: scalarizing half-densities requires a reference half-density; “dimensionless scalar amplitude” forces a `length^{d/2}` scale,
- optional universality hypotheses: constancy/background-freedom + “no fractional powers” restrictions,
- alternative scale-generation mechanisms: dimensional transmutation (RG-invariant scales) as a non-analytic scale source.

Rigorization hooks:

- treat as a *program note* with explicit hypothesis knobs; avoid promoting to Claim 1 without a dynamical existence theorem,
- if pursued, formalize the “integrality/analyticity sieve” as an explicit Diophantine constraint once “admissible coupling coordinates” are fixed.

### 7) Explicit “forward queue” items embedded in the RG-fundamental draft

The RG-fundamental note contains its own explicit TODO list (section “What This Paper Must Still Do”), including:

1. decide whether rooted-tree/Hopf-algebra material is core vs appendix,
2. make 3D Wilsonian fixed points explicit via a dimensionless coupling definition,
3. add an independent anchor for 1D `U(2)` contact interaction classification (OA-first) or mark `PENDING`.

These are direct task seeds for future bibliography + technical sharpening.

### 8) Bibliography “PENDING” ingest items in the main paper

The main paper flags deferred ingestion of:
`Dirac1933`, `Feynman1948`, `Connes1994`, `Landsman1998` (as `PENDING`).

Rigorization hook:

- for any theorem-grade claim depending on these, either ingest/cite standard references or downgrade to heuristic until anchored.

## Suggested additions to physbook task queue (actionable, not yet executed)

1. [done (Lean, minimal)] Semigroup→generator lemma: `Claim1lean/SemigroupGenerator.lean` with note `research/workspace/notes/theorems/2026-02-10-claim1-lean-semigroup-generator-lemma.md`.
2. Formalize L² half-density scalarization equivalence as a unitary map (reference half-density change).
3. Promote the Gaussian kernel semigroup normalization (`t^{-d/2}`) to a theorem with stated analytic conditions (Euclidean or `i0`).
4. Package the Schur-complement + determinant prefactor template and link it to Van Vleck/mixed Hessians.
5. Formalize point-splitting limit `(δ(·+ε)−δ)/ε → δ'` and record sign conventions once.
6. If Planck-area lane is kept: formalize the hypothesis ladder and the “dimension sieve” constraints with explicit coupling admissibility rule.

## Validation Contract (for this narrative extraction note)

### Assumptions

1. This is a reading/extraction pass; no new proof is claimed.
2. Any “rigorization hook” is a suggested path, not a completed derivation.

### Units and dimensions check

1. Dimensional-analysis statements are copied from the sources and must be re-checked when promoted.

### Symmetry/conservation checks

1. No new symmetry claim is asserted here beyond what was read.

### Independent cross-check path

Reproduce by opening the listed `../physarticle/...` Markdown sources and searching for the keywords:
`half-density`, `t^{-d/2}`, `Schur`, `delta'`, `contact term`, `scalarization`, `dimension sieve`, `PENDING`.

### Confidence statement

High confidence the bullets reflect text present in the read sources; medium confidence on which hooks will be “Lean-feasible” without additional framework work.

### Reproducibility metadata

1. host repo: `/Users/arivero/physbook`
2. scanned repo: `/Users/arivero/physarticle`
3. shell: `zsh`
4. date anchor: 2026-02-10 (US)

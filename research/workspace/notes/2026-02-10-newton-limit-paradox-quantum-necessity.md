# Newton Limit Paradox: Why Quantum Mechanics Is Forced (Research Question)

Date: 2026-02-10 (US)

## Long Thinking Goal

Identify a precise mathematical paradox/inconsistency in the Newtonian/classical
limit program that:

1. makes the naive "Newton-only" limit unrigorous (or non-unique / coordinate-dependent),
2. is resolved by introducing quantum-mechanical structure (amplitudes / half-densities / phases),
3. mirrors (in spirit) how Newtonian calculus resolves Zeno-style paradoxes by
   changing what "limit" means.

This is a research question and framing device, not yet a theorem claim.

## Working Hypothesis (Candidate Paradox Class)

The paradox is not "classical mechanics contradicts itself" in isolation; it is:

> If you demand a *local* composition/refinement principle and a *coordinate-free*
> continuum limit for variational selection ("extremals dominate"), then a
> positive density-level object is not stable under refinement.
> The stable object lives one level up: a complex amplitude / geometric
> \(1/2\)-density kernel whose modulus-square produces densities only after
> a weak/averaged limit (Born scaling).

This is the programmatic shape already visible in the static core:

- amplitude normalization is forced (`ε^{-1/2}` in 1D stationary phase),
- density-level limits can fail pointwise when multiple critical points exist
  (oscillatory cross terms), but become meaningful after additional weak-limit
  prescriptions.

Primary internal anchor:
`research/workspace/notes/theorems/2026-02-08-claim1-scoped-bridge-statement.md`.

## Candidate Obstruction: No Canonical Lebesgue Measure on Path Space

One precise obstruction to a naive "Newton-only" refinement slogan

> "time-slice, integrate over trajectories, and send `Δt → 0`"

is that a literal translation-invariant Lebesgue/Haar-type measure on an
infinite-dimensional path space does not exist in the sense needed for
"refine and integrate" to be a canonical limit statement.

Standard formulation (informal):
in an infinite-dimensional separable Banach space `X`, there is no nontrivial
translation-invariant Borel measure that is finite on a nonempty open set.

Operational moral for this workspace:
`Dq` in a path integral is not an ordinary countably additive Lebesgue measure;
refinement limits are *constructions* that must specify normalization and
regulator/subtraction compatibility data. Semigroup structure and generator
lemmas (beta functions) are the natural consistency language for these
constructions.

Internal pointer:
`../physarticle/blackboards/2026-02-10-no-lebesgue-measure-in-infinite-dim.md`
(standard proof sketch via packing disjoint translates).

## Concrete "Rigorous Targets" Suggested by This Question

1. **Composition forces normalization (semigroup constraint):**
   show that requiring a short-time convolution/semigroup law forces the
   \(t^{-d/2}\) normalization and determinant prefactors (Van Vleck / Hessian
   patterns). This is the cleanest "Zeno-analogue": a consistency axiom forces
   the scaling that makes limits exist.
2. **Half-density as the coordinate-free carrier:**
   explain (and formalize) why kernels must be geometric \(1/2\)-densities for
   convolution to be coordinate invariant (groupoid viewpoint), with density
   recovered only after squaring.
3. **Multi-branch classical limits are ill-posed without amplitude structure:**
   prove that naive density-level limits can fail (non-existence / non-uniqueness)
   in multi-critical settings unless one keeps phase information and/or weakly
   averages oscillatory cross terms.
4. **Refinement limits require limit-swap theorems:**
   formalize clean "commuting limit" lemmas (refinement/exhaustion vs
   de-regularization `η→0+`) with explicit quantitative tail/mismatch envelopes.

## How This Connects to Current Work

- Claim 1 already packages a delta-of-variation ladder (static -> QM -> QFT);
  this question asks for the exact mathematical reason the ladder cannot be
  made into a density-only object without introducing amplitudes.
- Recent Lean support work (AN-33L/AN-34L) is directly relevant to item (4):
  it supplies explicit transfer and mismatch-penalty wrappers for swapping
  limits and transporting projective defects across regularizations.
- New Lean support work (2026-02-10) provides a minimal semigroup→generator
  lemma: right-derivative at `0` + semigroup composition implies a beta-function
  generator and a right-derivative ODE for orbits; see
  `research/workspace/notes/theorems/2026-02-10-claim1-lean-semigroup-generator-lemma.md`.
- New Lean support work (2026-02-10) also provides a Schur-complement determinant
  prefactor template for 2×2 block matrices (Van Vleck / Gaussian-elimination
  backbone); see
  `research/workspace/notes/theorems/2026-02-10-claim1-lean-schur-complement-determinant-template.md`.
- New Lean support work (2026-02-10) also adds a 1D Gaussian semigroup + diagonal prefactor
  anchor (variance-addition semigroup; `1/sqrt(2*pi*v)` at the diagonal); see
  `research/workspace/notes/theorems/2026-02-10-claim1-lean-gaussian-semigroup-normalization.md`.

## Actionable Next Steps (Short List)

1. [partial] Semigroup-normalization lane: a 1D Gaussian semigroup + diagonal prefactor anchor
   is now machine-checked; next is a full `t^{-d/2}` kernel statement in `d` dimensions.
2. [done] In Lean: build a minimal "commuting-limit wrapper" lemma (AN-33L-C) on top of
   the AN-33L-B transfer bounds.
3. [done] In Lean: formalize a minimal semigroup→generator lemma for coarse-graining maps
   (`Claim1lean/SemigroupGenerator.lean`).
4. Extract from `research/workspace/notes/audits/2026-02-10-physarticle-tex-claims-extraction.md`
   the exact semigroup and Van Vleck templates to use as the narrative bridge.

## Confidence / Status

Status: speculative framing, with multiple concrete theorem targets identified.

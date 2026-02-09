# Wikipedia Baseline Definitions and Skepticism Protocol

Date: 2026-02-09 (US)
Purpose: standardize core terminology with public baseline definitions, while preventing over-trust in encyclopedia wording.

## Baseline Definitions (Wikipedia, paraphrased)

1. `probability amplitude`
   - Baseline: a complex quantity whose modulus squared gives measurement probabilities.
   - Workspace use: default term for static QM-facing narrative.
   - Source: https://en.wikipedia.org/wiki/Probability_amplitude

2. `Born rule`
   - Baseline: rule mapping wavefunction/amplitude data to probabilities.
   - Workspace use: interpretation layer for amplitude-to-density map.
   - Source: https://en.wikipedia.org/wiki/Born_rule

3. `path integral formulation`
   - Baseline: quantum formulation equivalent to Schrödinger/Heisenberg pictures, using sums/integrals over histories.
   - Workspace use: target equivalence language for Goal 1B dynamics paper.
   - Source: https://en.wikipedia.org/wiki/Path_integral_formulation

4. `propagator` / `transition amplitude`
   - Baseline: kernel giving amplitude for evolution between spacetime points or states.
   - Workspace use: preferred dynamics term in path-integral sections.
   - Source: https://en.wikipedia.org/wiki/Propagator

5. `Schwinger-Dyson equation`
   - Baseline: hierarchy of exact quantum-field identities for Green's functions.
   - Workspace use: identity family for consistency checks, not standalone existence proof.
   - Source: https://en.wikipedia.org/wiki/Schwinger%E2%80%93Dyson_equation

6. `geometric quantization` / `half-form`
   - Baseline: geometric quantization framework includes half-form (metaplectic) correction.
   - Workspace use: reserve `half-form` for geometric-quantization sections.
   - Source: https://en.wikipedia.org/wiki/Geometric_quantization

7. `density on a manifold` / `1/2-density`
   - Baseline: densities are coordinate-invariant integration objects; half-densities are square-root objects.
   - Workspace use: reserve `1/2-density` for explicit geometric kernel calculus.
   - Source: https://en.wikipedia.org/wiki/Density_on_a_manifold

8. `Lie groupoid`
   - Baseline: a groupoid with smooth manifold structure compatible with source/target/composition maps.
   - Workspace use: structural language for tangent-groupoid composition.
   - Source: https://en.wikipedia.org/wiki/Lie_groupoid

## Workspace Terminology Rule

1. Physics narrative:
   - use `probability amplitude` (statics),
   - use `transition amplitude`/`propagator` (dynamics).
2. Geometric quantization:
   - use `half-form`/`metaplectic correction`.
3. Kernel geometry and groupoids:
   - use `1/2-density` (or `half-density`) only when the object is literally a section of a square-root density bundle.

## Skepticism Protocol for Future Agents

1. Treat Wikipedia as orientation, not theorem authority.
2. Never promote a claim to `proved` using only Wikipedia definitions.
3. For every terminology-critical claim, add at least one non-Wikipedia technical source (paper, monograph, or official lecture notes).
4. If terminology and proof obligations diverge, prioritize the formal statement and mark terminology as `provisional`.
5. Record access date and link for each borrowed definition because page wording can drift.
6. If a term is overloaded across subfields, state the local definition explicitly before proving anything.

## Minimal Citation Hygiene

When a future note imports a term from this file, include:

1. the term,
2. the local definition actually used,
3. one primary technical source used for validation beyond Wikipedia.


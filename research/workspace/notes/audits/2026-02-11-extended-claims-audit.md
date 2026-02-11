# Extended Claims Audit (Claims 11-17)

Date: 2026-02-11 (US)
Source: `conv_patched.md` and existing theorem notes
Extends: `research/workspace/notes/audits/2026-02-08-top10-claim-audit.md`

## New Claims Identified

### Claim 11: Planck Area Quantization Forces 3+1 Dimensions via Inverse-Square Law

**Statement**: For a generic force law `F = G m m' / r^q`, demanding that
the area `A(t_P)` swept in Planck time equals a multiple of Planck area
produces a dimensional relation where Newton's constant cancels only for
`q = 2` (inverse-square law). If the force originates from a wave propagator
(Fourier transform), this fixes spacetime to 3+1 dimensions.

**Location**: `conv_patched.md:1717-1730`

**Label**: `heuristic`

**Score**: 5.5

**Rationale**: The dimensional analysis is explicit and reproducible, but
the "wave propagator origin" step is an assumption without rigorous derivation.
The cancellation at `q=2` is algebraically verifiable.

**Upgrade path**:
1. Formalize the Fourier-transform-to-propagator step with explicit assumptions,
2. Produce a symbolic CAS verification of the dimensional cancellation,
3. Clarify the logical status (is this a derivation or a consistency condition?).

### Claim 12: Uncertainty Principle Forces Inverse-Square Force from Virtual Exchange

**Statement**: If the preferred wavelength for exchanged virtual quanta scales
as the inter-particle distance `r`, and the exchange occurs within the
uncertainty-principle time `Δt ~ r/c`, then `F = Δp/Δt ~ ħc/r²`. For massive
mediators, the same argument with `Δp = (1/c)√(E² - m²c⁴)` and `Δt = r/c`
produces an approximation to Yukawa-type short-range forces.

**Location**: `conv_patched.md:1732-1756`

**Label**: `heuristic`

**Score**: 5.0

**Rationale**: The argument is physically motivated and yields the correct
scaling, but the `Δt = r/c` assumption is ad hoc for the massive case. The
connection to virtual particles and off-shell contributions is stated but not
made theorem-grade.

**Upgrade path**:
1. Derive the `Δt` prescription from a proper time-energy uncertainty relation,
2. Compare with the exact Yukawa potential at finite mass,
3. Quantify the quality of the short-distance approximation.

### Claim 13: Action Additivity + Composition Uniquely Forces `exp(iS/ħ)` Kernel

**Statement**: Given (i) locality in time (propagator composes via
Chapman-Kolmogorov), (ii) superposition (intermediate alternatives add),
and (iii) compatibility with probability interpretation, the unique
multiplicative weight satisfying `W[q₁ ⋆ q₂] = W[q₁] W[q₂]` with an additive
functional is `W[q] = exp(iS[q]/ħ)`, where `S` is the classical action.

**Location**: `conv_patched.md:2226-2267`

**Label**: `proved` (within stated axioms)

**Score**: 8.0

**Rationale**: The argument is mathematically clean: multiplicativity +
additivity ⟹ exponential. The identification of `S` as the unique natural
additive functional is standard but relies on regularity assumptions. The
connection to Dirac/Feynman is well-documented.

**Upgrade path**:
1. State the regularity hypotheses precisely (continuity, measurability),
2. Address alternative additive functionals (topological terms, boundary terms),
3. Formalize the uniqueness claim with a no-go for non-exponential weights.

### Claim 14: Amplitudes as Half-Densities on Tangent Groupoid Algebras

**Statement**: On a Lie groupoid, convolution algebras are canonically
formulated using half-densities. The quantum amplitude `A_ε(O) = ε^{-1/2} ∫ exp(if(x)/ε) O(x) dx`
is naturally a half-density, and `|A_ε|²` recovers the full density
(probability). This provides a geometric "why a square root?" answer: amplitudes
are half-densities; probabilities are densities.

**Location**: `conv_patched.md:932-969`

**Label**: `heuristic`

**Score**: 7.0

**Rationale**: The half-density interpretation is well-established in
noncommutative geometry (Connes). The static case (`dim 0`) is proved in
the conversation. The connection to full path-integral (infinite-dimensional)
half-densities remains scoped.

**Upgrade path**:
1. Extend the static proof to finite-dimensional sliced path integrals,
2. Connect to the existing Lean formalization of half-density structures,
3. Prove the Van Vleck determinant is literally a half-density transformation.

### Claim 15: Democritean Refinement Argument → Quantum Mechanics Necessity

**Statement**: The structural pattern "defining a quantity by summing local
pieces requires stability under refinement" applies to:
(a) geometry (volume additivity → exhaustion → measure theory),
(b) mechanics (action additivity → path composition → quantum amplitudes).
Classical trajectories are limiting objects (stationary-phase saddle points)
of the quantum theory, not independent constructions.

**Location**: `conv_patched.md:2140-2299`

**Label**: `speculative`

**Score**: 4.5

**Rationale**: The narrative is mathematically motivated and physically
compelling, but the "unavoidability" claim depends on specific axioms
(composition + superposition + probability) whose necessity is philosophical
rather than theorem-grade. The Hilbert 3rd problem connection (Dehn invariant
as obstruction) is a genuine mathematical insight.

**Upgrade path**:
1. State the axioms precisely and prove that violating any one leads to
   inconsistency with known physics,
2. Formalize the Dehn-invariant analogy into a precise mathematical statement,
3. Connect to rigorous constructive QFT results (Osterwalder-Schrader).

### Claim 16: Two-Body Planck Area Quantization and Standard Model Mass Scales

**Statement**: In the two-body gravitational problem with both orbiting
bodies subject to Planck area quantization `A_i(t_P) = n_i A_P`, the
center-of-mass condition yields `m₁² n₁ = m₂² n₂`. Taking extreme mass
ratios with small quantum numbers produces relationships involving the
Planck mass that span standard model mass scales.

**Location**: `conv_patched.md:1822-1878`

**Label**: `speculative`

**Score**: 3.5

**Rationale**: The algebraic derivation is explicit, but the physical
interpretation ("planckian scales can study the span of masses in the SM")
is acknowledged as speculative by the author. The `m₁ = 175 GeV` (top quark)
example is suggestive but not derived from first principles.

**Upgrade path**:
1. Classify which SM mass ratios can be reproduced and which cannot,
2. Determine if the relation `m₁² n₁ = m₂² n₂` has a group-theoretic origin,
3. Compare with known Regge trajectory / string theory mass relations.

### Claim 17: Schwinger-Dyson Identity as RG Invariant via Ehrenfest Correspondence

**Statement**: The identity `⟨δL/δφ⟩ = δ(1/ħ)` (equation 11 in the source)
is automatically invariant under RG transformations of the dressed series.
This connects the Schwinger-Dyson equations to Ehrenfest's theorem and
provides an interpretation of RG invariance as conservation of the equation
of motion in expectation.

**Location**: `conv_patched.md:800-811`

**Label**: `heuristic`

**Score**: 6.0

**Rationale**: The formal manipulation is correct within finite-dimensional
models. The distributional interpretation of `δ(1/ħ)` is controlled. The
infinite-dimensional (field theory) extension requires renormalization and
operator ordering control.

**Upgrade path**:
1. Prove the identity rigorously in the finite-dimensional cylinder models
   (already partially done in Claim 1 AN-29 Schwinger-Dyson formalization),
2. State the renormalization conditions needed for the field-theory extension,
3. Connect to the Connes-Kreimer rooted-tree RG framework.

## Summary Score Table

| Claim | Score | Label |
|---|---:|---|
| 11 (Planck area → 3+1D) | 5.5 | heuristic |
| 12 (Uncertainty → inverse-square) | 5.0 | heuristic |
| 13 (Action additivity → exp(iS/ħ)) | 8.0 | proved (scoped) |
| 14 (Half-density groupoid) | 7.0 | heuristic |
| 15 (Democritean refinement → QM) | 4.5 | speculative |
| 16 (Two-body Planck area + SM) | 3.5 | speculative |
| 17 (SD as RG invariant) | 6.0 | heuristic |

Extended mean (Claims 1-17):
\[
\bar S_{1-17} = \frac{9.77 + 9.1 + 8.95 + 9.1 + 9.1 + 9.6 + 9.65 + 7.99 + 8.41 + 9.65 + 5.5 + 5.0 + 8.0 + 7.0 + 4.5 + 3.5 + 6.0}{17} \approx 7.69.
\]

## Focus Lock Assessment

Claims that directly support the foundational axis:
- **Variational-distribution core**: Claims 13, 14, 15, 17 (strongest alignment)
- **Geometry-of-force bridge**: Claims 11, 12 (moderate alignment)
- **Scale-control core**: Claims 16, 17 (moderate alignment)

## Reproducibility Metadata

1. Source: `conv_patched.md` and existing theorem notes,
2. Date anchor: 2026-02-11 (US).
3. Claim 13-17 verification scripts (2026-02-11): `python3.12 research/workspace/simulations/claim13_action_additivity_exp_kernel_check.py`, `python3.12 research/workspace/simulations/claim14_halfdensity_groupoid_born_rule_check.py`, `python3.12 research/workspace/simulations/claim15_democritean_refinement_check.py`, `python3.12 research/workspace/simulations/claim16_twobody_planck_area_sm_check.py`, `python3.12 research/workspace/simulations/claim17_sd_rg_invariant_check.py` (all checks passed).

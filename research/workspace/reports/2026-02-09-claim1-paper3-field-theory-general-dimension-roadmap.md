# Paper 3: Field-Theory Consistency Across Spacetime Dimension

Date: 2026-02-09 (US)

## Working Title

Field-Theory Consistency Across Spacetime Dimension: General-Dimension Program, Gates, and Literature Anchors

## Abstract

This paper sets a dimension-indexed field-theory program with explicit closure
gates: regulated existence, continuum existence, and reconstruction. It does
not claim full interacting closure in all dimensions. Current progress
establishes a scoped \(d=3\) closure in one compact-spin interacting Euclidean
subclass; AN-24 removes the hard cutoff in a local-renormalized channel, and
AN-26 plus AN-26B close SD test-side \(C_b^1\) extension with explicit
tail-control and insertion-moment verification in-branch. AN-27 then transfers
the widened local class to the oscillatory/de-regularized branch under
explicit non-vanishing and contour-envelope hypotheses. AN-28 extends that
branch to disconnected nonlocal cylinders, and AN-29 adds explicit
refinement-Cauchy rates plus denominator bookkeeping for their continuum
extraction in the same scoped lane. AN-30 extends this further to finite
graph-indexed multi-block families with explicit combinatorial constants and
projective-consistency closure. AN-31 then lifts AN-30 to uniformly locally
finite exhaustion families with summability-weighted tail control. AN-32
extends AN-31 from cylinder classes to weighted-local observable/SD-test
classes with explicit exhaustion-uniform insertion-tail estimates. AN-33A now
adds a drafted graph-decay nonlocal weighted-local theorem skeleton with an
explicit Lean-obligation map for denominator-rate bookkeeping, and AN-33B
closes that lane in the same scoped branch. AN-34A then replaces AN-33
denominator/numerator rate postulates by first-principles shell-tail
transmutation bounds in the same scoped branch. AN-33L/AN-34L-A then lifts
those one-sided envelopes to exhaustion-indexed pairwise transfer wrappers used
directly by AN-31 Cauchy/projective bookkeeping.

## Scope

In scope:

1. one framework covering \(d=2\), \(d=3\), \(d=4\), and \(d>4\),
2. explicit assumptions and failure gates by dimension,
3. source-backed baseline claims from standard literature.

Out of scope:

1. claiming a fully closed interacting \(d=4\) continuum theorem in this pass,
2. replacing constructive estimates by formal kernel language alone.

## Field Setup

For a local scalar prototype on \(\mathbb{R}^d\):
\[
S_d[\Phi]=\int_{\mathbb{R}^d}\left[\frac12 |\nabla\Phi|^2+\frac{m^2}{2}\Phi^2+\frac{\lambda}{4!}\Phi^4\right]\,d^dx.
\]
At finite cutoff/volume:
\[
\omega_{c,\Lambda,a,L}(F)=
\frac{\int e^{-cS_{d,\Lambda,a,L}[\Phi]}F[\Phi]\,D\Phi}
{\int e^{-cS_{d,\Lambda,a,L}[\Phi]}\,D\Phi},
\qquad \Re c>0.
\]

## Three Mandatory Gates

For each dimension branch \(\mathcal B_d\), closure means all three:

1. **G1 regulated existence:** finite cutoff and finite volume channel is well-defined.
2. **G2 continuum existence:** cutoff/volume removal has nontrivial limits.
3. **G3 reconstruction:** Euclidean channel maps to the intended physical QFT class.

## Dimension-Indexed Program Claim

1. \(d=2\): first full-closure candidate branch.
2. \(d=3\): next branch with superrenormalizable control targets.
3. \(d=4\): frontier branch; theorem-grade scoped statements and open assumptions must be separated.
4. \(d>4\): EFT/mean-field/triviality-guided branch unless a UV-complete model is fixed.

## What the Lean Chain Supports

Machine-checked finite-model modules provide reusable inequality templates for
small-parameter increment control and regularity bookkeeping.

Current limitation: these modules do not by themselves discharge field-level
G2/G3; they support the field program only after translation into
dimension-indexed bound propositions.

## Current \(d=3\) Branch Status (Scoped Closure + Open Gap)

Finite-volume \(d=3\) proposition with constants
\[
K_F=2\|F\|_\infty,\qquad
M_{B,a}=\frac{4|E_B|}{c_0m_0^2a^3},
\]
and bounds
\[
|F-\omega(F)|\le K_F,\qquad \omega(G_B)\le M_{B,a},
\]
uniform in \(L\) and \(\kappa\in[0,\kappa_*]\).

Renormalized finite-volume channel:
\[
G_{B,a}^{\mathrm{ren}}:=a^3G_B,\qquad
\omega(G_{B,a}^{\mathrm{ren}})\le M_B^{\mathrm{ren}},
\qquad
M_B^{\mathrm{ren}}=\frac{4|E_B|}{c_0m_0^2},
\]
uniform in \(a,L,\kappa\). This removes explicit \(a^{-3}\) constants from
finite-volume B5b inputs.

AN-23 closes B1--B4 in a concrete interacting compact-spin Euclidean subclass:

1. B1 local moments from \(|\phi|\le R\),
2. B2 local tightness from compact block marginals,
3. B3 denominator non-vanishing (\(Z>0\)),
4. B4 SD pass-through for boundary-vanishing local test class.

This upgrades the AN-22 candidate to scoped closure in that subclass.
AN-24 now removes hard-cutoff \(R\to\infty\) with B1-B4 preserved in a
local-renormalized compact-support channel.
AN-25 closes observable-side widening \(C_c\to C_b\).
AN-26 + AN-26B close SD test-side widening \(C_c^1\to C_b^1\) by combining the
Holder/Markov tail criterion with an explicit \(q=4/3\) insertion-moment bound.
AN-27 transfers this widened class to the oscillatory/de-regularized branch.
AN-28/AN-29 then extend to disconnected nonlocal cylinders with explicit
refinement-Cauchy and denominator-rate control in that same scoped branch.
AN-30 upgrades this to finite graph-indexed multi-block families with explicit
combinatorial rates and projective consistency in the refinement limit.
AN-31 lifts this to exhaustion families with explicit summable-tail Cauchy and
projective-defect control. AN-32 then lifts AN-31 to weighted-local
observable/SD-test classes with explicit insertion-tail bounds proportional to
weighted coefficient tails. AN-33A/AN-33B then extend this to graph-decay
nonlocal weighted-local channels with explicit denominator-rate normalized-state
bookkeeping. AN-34A then derives those denominator/numerator rate bounds from
first-principles shell-tail envelopes, preserving explicit normalized ratio
Cauchy rates. AN-33L/AN-34L-A now lifts these to exhaustion-indexed pairwise
rate wrappers (including additive/projective splitting form) in Lean.

## Literature Anchors

1. Osterwalder-Schrader I (1973): https://doi.org/10.1007/BF01645738
2. Osterwalder-Schrader II (1975): https://doi.org/10.1007/BF01608978
3. Wilson-Kogut (1974): https://doi.org/10.1016/0370-1573(74)90023-4
4. Guerra-Rosen-Simon \(P(\phi)_2\) (1975): https://doi.org/10.2307/1970985
5. Aizenman \(\phi^4_d\) triviality (1981): https://doi.org/10.1103/PhysRevLett.47.1
6. Aizenman-Duminil-Copin marginal triviality (2021): https://doi.org/10.4007/annals.2021.194.1.3

## Immediate Next Scientific Step

1. package projective-defect and de-regularization transfer lemmas on top of
   AN-33L/AN-34L-A exhaustion pairwise wrappers (AN-33L-B),
2. tighten reconstruction-facing interfaces by separating scoped proven rates
   from remaining G3 inputs in the \(d=3\to d=4\) frontier transition.

## Validation Contract

1. **Assumptions:** model class and dimension branch explicit in each statement;
   closure status reported only through G1/G2/G3.
2. **Units/dimensions:** \(S_d\) carries action dimension; phase/weight argument
   dimensionless.
3. **Independent checks:**
   - theorem/estimate channel (Lean where feasible, analytic where not),
   - bibliography check against standard references,
   - executable finite surrogates:
     - `python3.12 research/workspace/simulations/claim1_d3_finite_volume_centered_moment_bound_check.py`,
     - `python3.12 research/workspace/simulations/claim1_d3_renormalized_moment_channel_check.py`,
     - `python3.12 research/workspace/simulations/claim1_d3_an22_continuum_branch_proxy_check.py`,
     - `python3.12 research/workspace/simulations/claim1_d3_an23_compact_spin_closure_check.py`,
     - `python3.12 research/workspace/simulations/claim1_d3_an24_cutoff_lift_check.py`,
     - `python3.12 research/workspace/simulations/claim1_d3_an25_class_extension_check.py`,
     - `python3.12 research/workspace/simulations/claim1_d3_an26_tail_insertion_control_check.py`,
     - `python3.12 research/workspace/simulations/claim1_d3_an26b_insertion_lq_moment_check.py`,
     - `python3.12 research/workspace/simulations/claim1_d3_an27_oscillatory_dereg_transfer_check.py`,
     - `python3.12 research/workspace/simulations/claim1_d3_an28_nonlocal_cylinder_transfer_check.py`,
     - `python3.12 research/workspace/simulations/claim1_d3_an29_nonlocal_continuum_cauchy_check.py`,
     - `python3.12 research/workspace/simulations/claim1_d3_an30_multiblock_projective_consistency_check.py`,
     - `python3.12 research/workspace/simulations/claim1_d3_an31_exhaustion_summability_check.py`,
     - `python3.12 research/workspace/simulations/claim1_d3_an32_weighted_local_sdtest_check.py`,
     - `python3.12 research/workspace/simulations/claim1_d3_an33_graph_decay_nonlocal_weighted_local_check.py`,
     - `python3.12 research/workspace/simulations/claim1_d3_an34_firstprinciples_tail_rate_check.py`.
4. **Confidence statement:** this is a theorem-program with scoped \(d=3\)
   closure plus hard-cutoff lift and AN-25/AN-26/AN-26B class-extension closure
   in a scoped Euclidean branch; AN-27 closes oscillatory/de-regularized
   transfer, AN-28/AN-29 extend this to disconnected nonlocal cylinders with
   explicit refinement-Cauchy bookkeeping, and AN-30 extends further to finite
   graph-indexed multi-block projective consistency with explicit combinatorial
   constants. AN-31 lifts this to exhaustion-family summability control, and
   AN-32 lifts AN-31 to weighted-local observable/SD-test classes with explicit
   insertion-tail envelopes. AN-33 closes graph-decay nonlocal weighted-local
   denominator-rate bookkeeping in the same scoped branch, and AN-34A upgrades
   that lane by deriving rates from first-principles shell-tail envelopes.
   AN-33L/AN-34L-A lifts those bounds to exhaustion-indexed pairwise transfer
   wrappers aligned with AN-31 bookkeeping. Full global continuum interacting
   closure remains open.

## Reproducibility Metadata

1. date anchor: 2026-02-09 (US),
2. build toolchain: `/Library/TeX/texbin/pdflatex` (TeX Live 2025),
3. safe build script: `~/.codex/skills/pdflatex-safe-build/scripts/build_pdflatex_safe.sh`.

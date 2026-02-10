# Physarticle TeX Claim Extraction (Future Rigorization Queue)

Date: 2026-02-10 (US)

## Scope

Scanned TeX sources in the sibling repository `../physarticle/`:

- `../physarticle/paper/main.tex` (Newton → action → path integral → deformation → RG narrative)
- `../physarticle/papers/planck-area/main.tex` (half-density scaling + “universal area” sieve)
- `../physarticle/papers/rg-fundamental/main.tex` (RG-as-compatibility note + 2D delta worked model)

Goal: extract candidate claims (as stated there) and convert them into a queue of
“rigo(u)rization targets” (what to prove formally, what to cite, what to downgrade to heuristic).

This note is *not* a proof pass.

## Extracted Claims (by file)

### A) `../physarticle/paper/main.tex`

Taxonomy used in that paper: `Proposition` (intended math-valid under stated assumptions), `Derivation`, `Heuristic`.

**P0.1 (Additive refinement structure)** (`main.tex:171`)
- Claim: the discrete action `S_N` is additive over concatenated subintervals, hence suited for comparing refinements.
- Rigorization: fully standard (definition-level); keep as lemma with explicit statement of partitioning convention.

**P1.1 (Refinement limit of areal velocity)** (`main.tex:296`)
- Claim: equal-areas discrete invariant yields `dA/dt = ||L||/(2m)` in the refinement limit; also follows from zero torque for smooth central forces.
- Rigorization: cite standard mechanics (central force ⇒ conserved angular momentum ⇒ areal velocity constant); if desired, formalize the polygonal refinement model separately.

**P2.0 (Fundamental lemma, vector form)** (`main.tex:372`)
- Claim: if `∫ F·η = 0` for all compactly supported smooth test `η`, then `F=0` (pointwise on the open interval).
- Rigorization: standard functional analysis/variational calculus lemma; cite a textbook; Lean formalization is plausible in `mathlib` (in `Real`/`R^n`).

**P2.1 (Geometric–variational invariant equivalence)** (`main.tex:458`)
- Claim: `\dot A = (1/2) r^2 \dot θ = L_ang/(2m)` i.e. the area-law invariant equals the Noether charge statement.
- Rigorization: standard identity; depends on polar-coordinate definitions and `L_ang = m r^2 \dot θ`.

**P2.2 (Energy for autonomous central motion)** (`main.tex:470`)
- Claim: if `∂_t L = 0`, then energy `E = \dot q · ∂_{\dot q} L − L` is conserved; for central motion yields effective radial reduction.
- Rigorization: standard Noether theorem / Euler–Lagrange derivation with regularity assumptions.

**P3.1 (Weak stationarity statement)** (`main.tex:538`)
- Claim: `δS[q;η]=0` for all test `η` implies the Euler–Lagrange operator vanishes in distributions.
- Rigorization: standard integration-by-parts argument; precise assumptions needed: `q∈C^1`, appropriate regularity of `∂_q L`, `∂_{\dot q} L`, and boundary conditions.

**P3.2 (Localized probing under continuity)** (`main.tex:579`)
- Claim: if the Euler–Lagrange operator `F[q]` is continuous at `t0`, then weak stationarity implies `F[q](t0)=0` via mollifier tests.
- Rigorization: standard mollifier convergence; needs explicit continuity + dominated convergence hypotheses.

**P3.3 (Corner condition without impulse)** (`main.tex:610`)
- Claim: for a piecewise-`C^2` path with a velocity jump at `t0`, satisfying unforced E–L on each side, canonical momentum is continuous: `[∂_{\dot q} L]_-^+ = 0`.
- Rigorization: Weierstrass–Erdmann corner condition in a single-corner setting; formal proof via integrating E–L across `t0` under boundedness assumptions.

**P3.4 (Impulse force implies momentum jump)** (`main.tex:632`)
- Claim: for forced E–L with `J δ(t−t0)` on the RHS, canonical momentum jump equals `J`.
- Rigorization: distributional integration across `t0`; needs well-posedness of one-sided limits of `∂_{\dot q} L`.

**P4.1 (Exponential form under locality + composition)** (`main.tex:820`)
- Claim: multiplicative slice weights + additive-in-Δt log structure imply overall weight `∝ exp(c0 S_N[q])` (up to normalization/higher-order slicing corrections), with `c0` of dimension `1/action`.
- Rigorization: make hypotheses explicit (e.g. `log W_k = c0 L_k Δt_k + o(Δt_k)` uniformly); then it’s a standard “multiplicative ⇒ exponential of additive” lemma.

**P5.1 (Classical compatibility conditions)** (`main.tex:956`)
- Claim: for an associative `⋆_ℏ = fg + ℏ B1 + O(ℏ^2)`, the `O(ℏ)` commutator is determined by the antisymmetric part of `B1`.
- Rigorization: algebraic; can be proved in a few lines (formal power series setting).

**P5.2 (Equivalent star products, same classical limit)** (`main.tex:1035`)
- Claim: if `⋆` and `⋆'` are related by a formal automorphism `T_ℏ = id + ℏ T1 + …`, then they induce the same Poisson bracket at `ℏ→0` while differing at subleading terms.
- Rigorization: standard deformation-quantization equivalence; either cite a reference or prove directly by expanding to `O(ℏ)`.

**P6.1 (Renormalized observable as cutoff-stable limit)** (`main.tex:1115`)
- Claim: a “physical” observable is defined operationally as a cutoff-removed limit along tuned bare parameters `g_B(Λ)` if that limit exists/has controlled asymptotics.
- Rigorization: definitional/programmatic; for a theorem-grade version one must specify the model class, topology of convergence, and observable class.

**P6.2 (Flow generator from refinement semigroup)** (`main.tex:1198`)
- Claim: if the scale-change maps `W_{Λ→μ}` satisfy `id`, semigroup composition, and differentiability in `ln Λ`, then an infinitesimal generator (beta function vector field) exists.
- Rigorization: make the parameter space and differentiability precise; then it’s standard semigroup-to-generator (ODE on finite-dimensional manifold) if `W` acts smoothly on a finite-dimensional coordinate chart.

**P6.3 (Closure assumption for finite-parameter flow)** (`main.tex:1329`)
- Claim: finite-dimensional RG flows are only exact after choosing a closed truncation/ansatz; omitted operators break exact closure.
- Rigorization: conceptual but can be turned into a precise statement about projection of an infinite-dimensional flow to a finite-dimensional submanifold.

**P7.1 (Compatibility chain of limits)** (`main.tex:1370`)
- Claim: under the paper’s assumptions, one can impose simultaneously: weak E–L stationarity, semiclassical concentration (`ℏ→0`), Poisson recovery from star-commutator, and RG invariance constraints, as compatibility conditions in a staged construction.
- Rigorization: currently meta-structural; to make theorem-grade, split into separate theorems with explicit domains and prove implication arrows with precise notions of limit/concentration.

**P8.1 (Leading beta coefficient under analytic scheme change)** (`main.tex:1592`)
- Claim: under coupling reparametrization `g' = g + a g^2 + O(g^3)`, the leading `β(g) = −c g^2 + …` coefficient is invariant.
- Rigorization: straightforward formal computation (power series).

**P9.1 (Discretization-ordering equivalence class statement)** (`main.tex:1642`)
- Claim: different kernel discretizations corresponding to different orderings (e.g. left vs Weyl) share the same classical limit and differ by controlled `O(ℏ)` corrections.
- Rigorization: in the example given, this is explicit operator algebra; for a general theorem, specify symbol classes and operator domains.

**P10.1 (Refinement Compatibility Principle, RCP)** (`main.tex:1655`)
- Claim: admissible dynamics requires three compatibilities: (i) partition/refinement compatibility, (ii) representation/ordering compatibility (same classical limit), (iii) scale/RG compatibility (stable observables under scale changes).
- Rigorization: interpret as a definition/principle; to make it a theorem you’d need to fix a framework and prove that certain constructions satisfy RCP.

**P11.1 (Dimensional transmutation: RG-invariant bound-state scale)** (`main.tex:1801`)
- Claim: in the 2D delta interaction, define `κ_*` from `g_R(μ)` so it is μ-independent and sets the physical scale (bound state/scattering).
- Rigorization: can be made fully theorem-grade in the QM model using standard renormalized resolvent/T-matrix analysis; cite a reference or re-derive carefully with error bounds.

### B) `../physarticle/papers/planck-area/main.tex`

**P1.1 (No canonical “half-density = function” identification)** (`planck-area/main.tex:125`)
- Claim: identifying half-densities with scalar functions requires a choice of nowhere-vanishing reference half-density `σ_*` (equivalently density `ρ_* = σ_*^2`).
- Rigorization: differential-geometry standard; can be packaged as a lemma about line bundles and trivializations.

**P1.2 (Universal dimensionless amplitudes force a length^{d/2} constant)** (`planck-area/main.tex:158`)
- Claim: if scalar representatives of half-densities are required dimensionless, the reference half-density must carry `length^{d/2}` units; a constant `σ_*` is equivalent to choosing a universal `length^{d/2}` scale (area in `d=4`).
- Rigorization: dimensional-analysis statement + “choice of trivialization”; to make theorem-grade: specify unit assignment conventions and what “dimensionless” means in the chosen framework.

**P1.3 (Scalarization is a choice of measure, not new physics)** (`planck-area/main.tex:469`)
- Claim: choosing `σ_*` identifies `L^2` half-densities with `L^2(M, ρ_*)`, and different choices are unitarily equivalent scalar representations.
- Rigorization: functional-analytic statement about `L^2` isometries under weight change; can be written as a direct unitary map `U: f ↦ r^{-1} f` with `ρ ↦ r^2 ρ`.

### C) `../physarticle/papers/rg-fundamental/main.tex`

**P1.1 (Semigroup compatibility)** (`rg-fundamental/main.tex:84`)
- Claim: composable scale maps `W_{Λ→μ}` imply existence of an infinitesimal generator (beta functions) under differentiability assumptions.
- Overlap: same structural content as `paper/main.tex:P6.2`.

**P1.2 (RG-invariant scale from the delta interaction)** (`rg-fundamental/main.tex:258`)
- Claim: in the 2D delta model, `κ_*^2 := μ^2 exp( const / g_R(μ) )` is μ-invariant and rewrites the amplitude in terms of `κ_*`.
- Overlap: same as `paper/main.tex:P11.1` (worked model).

**P1.3 (Coarse-graining is a semigroup)** (`rg-fundamental/main.tex:610`)
- Claim: “integrate out modes” maps satisfy identity + associativity/composition, hence form a semigroup.
- Rigorization: define the coarse-graining operator precisely in a model class (Gaussian exact integration is done later as an explicit witness).

**P1.4 (Point interaction parameterizes a length scale)** (`rg-fundamental/main.tex:403`)
- Claim: s-wave solutions near `r=0` behave `A ln r + B + o(1)`; specifying a boundary condition relating `A,B` introduces a length scale `R` (self-adjoint extension parameter).
- Rigorization: spectral theory of Laplacian on punctured plane + SA extensions; cite standard results or prove in a functional-analytic framework.

**P1.5 (Semigroup property as associativity of integration)** (`rg-fundamental/main.tex:665`)
- Claim: coarse-graining by integrating out variables satisfies semigroup property by Fubini; in quadratic models corresponds to nested Schur complements.
- Rigorization: theorem-grade given integrability/positivity assumptions; in the Gaussian case can be proven explicitly.

**P1.6 (Canonical dimension of the delta coupling)** (`rg-fundamental/main.tex:442`)
- Claim: in `d` spatial dimensions, `g δ^{(d)}(x)` has `[g]=length^{d-2}` in `ℏ=c=1` units.
- Rigorization: pure dimensional analysis; specify the Hamiltonian conventions.

## Suggested Rigorization Targets (high value / low friction)

1. **Semigroup → generator lemmas** (`paper/main.tex:P6.2`, `rg-fundamental/main.tex:P1.1`):
   make a clean finite-dimensional “smooth semigroup of maps ⇒ ODE generator” lemma, suitable for Lean.
2. **Half-density scalarization unitary equivalence** (`planck-area/main.tex:P1.3`):
   this is a precise, short, and reusable lemma; can be formalized as an `L^2` isometry.
3. **Gaussian kernel semigroup normalization** (derivation `paper/main.tex:D4.1a`):
   promote to a theorem: convolution semigroup + quadratic phase ⇒ `t^{-d/2}` scaling, with explicit conditions (Euclidean time or `i0` regularization).
4. **2D delta dimensional transmutation** (`paper/main.tex:P11.1` / `rg-fundamental/main.tex:P1.2`):
   either cite a standard reference carefully or write a self-contained proof with clear regulator + subtraction scheme and error control.

## Validation Contract (for this extraction note)

### Assumptions

1. This is a *reading/extraction* pass of existing TeX text.
2. No claim listed here is re-proved in this note.
3. Line numbers refer to the TeX files as present on disk on 2026-02-10.

### Units and dimensions check

1. No new physical quantity is introduced here; “units” statements are copied from the scanned notes and should be re-checked during rigorization.

### Symmetry and conservation checks

1. No new symmetry statement is asserted here beyond the extracted claims.

### Independent cross-check path

Reproduce extraction via:

```bash
rg -n -F '\\texttt{Proposition' ../physarticle/paper/main.tex
rg -n -F '\\texttt{Proposition' ../physarticle/papers/planck-area/main.tex
rg -n -F '\\texttt{Proposition' ../physarticle/papers/rg-fundamental/main.tex
```

### Confidence statement

High confidence that the proposition IDs/titles are correctly extracted; medium confidence that the one-line paraphrases match intended scope (requires deeper proof-reading per proposition).

### Reproducibility metadata

1. host repo: `/Users/arivero/physbook`
2. scanned repo: `/Users/arivero/physarticle`
3. shell: `zsh`
4. date anchor: 2026-02-10 (US)


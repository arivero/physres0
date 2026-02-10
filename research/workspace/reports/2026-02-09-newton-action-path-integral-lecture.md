# From Newton to the Path Integral: A Foundational Lecture Note

Date: 2026-02-09  
Status: Working manuscript (foundational synthesis)

## 0. Aim

This note gives a single technical storyline for the corpus:

1. Newton’s finite-step geometric conservation law,
2. action-based reduction and discriminant orbit structure,
3. distributional/oscillatory emergence of amplitude weighting,
4. controlled refinement (\(h\), \(\tau_\mu\), Schwinger-Dyson),
5. field-theoretic extension.

The target is a first-month QFT companion narrative with explicit mathematical dependencies.

### Quick Definitions

1. `c-parameter`:
   \[
   c=(\eta-i/h)\kappa.
   \]
2. `c-invariant`:
   unchanged under parameter changes that keep \(c\) fixed (equivalently, constant on a \(\tau_\mu\)-orbit).
3. `de-regularization`:
   the one-sided limit \(\eta\to0^+\) from damped oscillatory kernels.
4. `terminology guardrail`:
   use probability/transition amplitude as default physics language; reserve geometric \(1/2\)-density for explicit kernel-bundle statements.

## 1. Newton’s Seed: Finite-Step Invariant Before the Limit

For central-force polygonal evolution (equal time steps \(\Delta t\)), equal swept triangles are exact at the discrete level.  
Angular momentum conservation is encoded geometrically:
\[
\Delta A_n=\frac12 |r_n\times \Delta r_n|,
\qquad
\frac{\Delta A_n}{\Delta t}=\frac{|L_n|}{2m}.
\]
Central impulse gives \(r_n\times \Delta p_n=0\), so \(\Delta A_n\) is step-invariant.

The continuum law is then a controlled refinement:
\[
\Delta t\to0,\qquad
\Delta A_n\to0,\qquad
\frac{\Delta A_n}{\Delta t}\to \text{finite constant}.
\]
The important logic is: exact finite-step structure first, limit second.

## 2. Action Reduction as Common Mechanics

For a Lagrangian action \(S=\int L(q,\dot q)\,d\lambda\):

1. time-translation symmetry gives conserved \(E\),
2. rotational symmetry gives conserved \(L\),
3. cyclic elimination reduces to a 1D radial problem
   \[
   p_r^2=\mathcal R(r;E,L,\dots).
   \]

Orbit classes are read from turning-point geometry:

1. allowed region: \(\mathcal R(r)\ge0\),
2. bounded non-circular branch: two turning points,
3. branch boundaries: double root
   \[
   \mathcal R(r_\star)=0,\qquad \mathcal R'(r_\star)=0.
   \]

This is the same mechanism in:

1. SR Coulomb (\(\alpha^2\)-classified regimes),
2. Schwarzschild fixed-energy interval and separatrix/ISCO,
3. probe dynamics in gauge-defined static \(V(r)\).

References in workspace:

- `research/workspace/notes/theorems/2026-02-08-claim3-coulomb-phase-classification.md`
- `research/workspace/notes/theorems/2026-02-08-claim6-schwarzschild-fixed-energy-interval.md`
- `research/workspace/reports/2026-02-09-claim9-gauge-phase-long-range-paper.tex`
- `research/workspace/notes/theorems/2026-02-09-foundational-action-reduction-unification.md`

## 3. Static Variational Problem as Distribution

For smooth \(f\), classical extrema are encoded by
\[
\delta(f'(x)).
\]
Under nondegenerate critical points \(x_i\):
\[
\delta(f'(x))
=
\sum_i \frac{\delta(x-x_i)}{|f''(x_i)|}.
\]

Fourier representation
\[
\delta(u)=\frac{1}{2\pi}\int e^{izu}\,dz
\]
introduces oscillatory exponentials already at static level.

The oscillatory amplitude expression
\[
A_\varepsilon(O)=\varepsilon^{-1/2}\int e^{\frac{i}{\varepsilon}f(x)}O(x)\,dx
\]
has
\[
|A_\varepsilon(O)|^2
\to
2\pi\langle \delta(f'),|O|^2\rangle
\]
in the stationary-phase/nondegenerate setting.  
This is the amplitude-to-density pattern and motivates probability-amplitude language; in geometric kernel calculus the same object is represented as a geometric \(1/2\)-density.

References in workspace:

- `research/workspace/notes/theorems/2026-02-08-claim1-discrete-variational-delta-lemmas.md`
- `research/workspace/notes/theorems/2026-02-08-claim1-manifold-halfdensity-convolution.md`
- `research/workspace/notes/theorems/2026-02-08-claim1-groupoid-halfdensity-theorem-pack.md`

## 4. From Static to Time Histories

Replacing \(f\) by action \(S[\phi]\), classical paths solve
\[
\frac{\delta S}{\delta \phi}=0.
\]
The formal object
\[
\delta\!\left(\frac{\delta S}{\delta\phi}\right)
\]
is regularized via oscillatory weighting of histories, leading to path-integral form.

Consistency of refinement/composition introduces a surviving scale parameter \(h\) (identified physically with \(\hbar\) in standard QM/QFT usage), and scale-flow covariance:
\[
\tau_\mu:\ (\kappa,\eta,h)\mapsto(\mu\kappa,\eta/\mu,\mu h),
\]
with dressed-state invariance under \(\tau_\mu\) in the scoped framework.

References in workspace:

- `research/workspace/notes/theorems/2026-02-09-claim1-scale-flow-covariance.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-fd-schwinger-dyson-identity.md`

## 5. Field-Theoretic Lift and Eq.(11)-Type Structure

In field form, Euler-Lagrange structure lifts to Schwinger-Dyson identities by functional integration by parts.  
In the scoped finite-dimensional model family, this is theoremized as:
\[
\int \partial_i\!\left(e^{-cS}\psi\right)=0
\;\Rightarrow\;
\left\langle \partial_i\psi\right\rangle
=
c\left\langle \psi\,\partial_i S\right\rangle.
\]
This is the rigorous version of the Eq.(11)-type closure thread in the corpus.

Field-level existence is dimension-dependent and should be tracked explicitly:

1. \(d=2\): strongest constructive continuum control in many classes (first closure target).
2. \(d=3\): substantial control for superrenormalizable branches (second closure target).
3. \(d=4\): physically central but hardest/open in key interacting cases (frontier with explicit hypotheses).
4. \(d>4\): typically EFT/nonrenormalizable branch for generic local interactions.

So the Claim 1 field program should escalate \(d=2\to d=3\to d=4\), rather than claim one-shot dimension-independent closure.

## 6. Current Claim 1 Closure Boundary

The scoped bridge now includes:

1. exact projective cylinder consistency,
2. \(\eta\to0^+\) de-regularization in several interacting classes,
3. large-\(N\) non-factorized quadratic and quartic tails,
4. finite-\(g\) non-perturbative multi-mode quartic control (Euclidean and oscillatory regularized),
5. \(\eta\to0^+\) closure for that multi-mode quartic sector.

Primary artifacts:

- `research/workspace/reports/2026-02-09-claim1-scoped-complete-proof.tex`
- `research/workspace/notes/theorems/2026-02-09-claim1-multimode-quartic-dereg-eta0.md`

Remaining frontier:

1. full continuum/global interacting equivalence beyond scoped classes,
2. uniform renormalization/channel control in truly field-theoretic limits.

Execution notes for this frontier:

- `research/workspace/notes/theorems/2026-02-09-claim1-three-level-program.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-field-dimension-existence-roadmap.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d2-field-cylinder-candidate.md`

### Claim maturity snapshot (audit, 2026-02-10 US)

The canonical score table lives in:
`research/workspace/notes/audits/2026-02-08-top10-claim-audit.md` (Section “Claim Maturity Scores (0-10)”).

| Claim | Score | Closure boundary (date-anchored summary) |
|---:|---:|---|
| 1 | 9.6 | Scoped theorem-grade closure in a nontrivial oscillatory/projective class (statics/dynamics plus a dimension-gated \(d=2\to d=3\) field branch), with explicit remaining global interacting and reconstruction gaps. |
| 2 | 9.0 | Local asymptotic theorem closure is strong; global phase-space completion remains open. |
| 3 | 8.9 | SR Coulomb phase portrait and global/asymptotic time structure are theorem-closed in the scoped model. |
| 4 | 9.0 | \(n=3\) Duffing reduction and global-time/topology classification are theorem-grade in scoped model. |
| 5 | 9.0 | D-dimensional GR matching is closed in the conventions used. |
| 6 | 9.5 | Fixed-energy Schwarzschild bound-orbit interval and separatrix structure are fully explicit and cross-checked. |
| 7 | 9.5 | ISCO threshold statement is canonical and correctly framed with unit conventions. |
| 8 | 7.8 | Static baseline and rotating regime maps exist with explicit unresolved sectors (especially in multi-spin \(D\ge 6\) lanes). |
| 9 | 8.2 | Screened-Abelian Yukawa branch is theorem-closed; non-Abelian confining branch is closed at scoped extraction-theorem level with strong-coupling derivation and a \(\beta\)-transfer lane; first-principles transfer control and dynamical-matter string-breaking remain open. |
| 10 | 9.5 | Benchmark inequalities and threshold regimes are explicit and validated. |

## 7. Dependency Graph (Explicit)

```text
Newton finite-step area invariance
  -> action additivity + symmetry charges (E, L)
     -> 1D radial reduction p_r^2 = R(r)
        -> double-root boundaries (circular/separatrix/threshold)
           -> SR Coulomb regimes (Claim 3)
           -> Schwarzschild intervals + ISCO (Claims 6,7)
           -> gauge-phase static probe branches (Claim 9 map)

Static variational distribution δ(f')
  -> Fourier/oscillatory representation
     -> oscillatory amplitude |A|^2 structure
        -> geometric 1/2-density/groupoid formulation
           -> path-time slicing + RG-style control (tau flow)
              -> Schwinger-Dyson lifted equations
                 -> scoped Claim 1 theorem chain
                    -> large-N non-factorized interacting tails
                       -> finite-g nonperturbative + η->0+ closures
```

## 8. Groupoid/\(\tau_\mu\)/Schwinger-Dyson Unified Sheet

The dependency requested on the foundational queue is now formalized in:

- `research/workspace/notes/theorems/2026-02-09-claim1-groupoid-tau-sd-dependency-sheet.md`

Core fixed-parameter identity:
\[
c=(\eta-i/h)\kappa
\]
is preserved by
\[
\tau_\mu:(\kappa,\eta,h)\mapsto(\mu\kappa,\eta/\mu,\mu h),
\]
and Schwinger-Dyson Eq.(11)-type identities are invariant because they depend on the kernel only through \(c\).

This closes the conceptual link:
groupoid scaling intuition \(\leftrightarrow\) dressed flow covariance \(\leftrightarrow\) SD closures.

## 9. Minimal “What Is Forced” Statement

In this program, path-integral-type oscillatory weighting is not introduced as optional aesthetics; it is the structurally stable way to combine:

1. localization on variational extrema (distributional viewpoint),
2. multiplicative composition under slicing (action additivity),
3. controlled refinement with a surviving scale parameter.

That is the precise sense in which quantum weighting appears as the consistent correction/completion of naive classical refinement.

## 10. Reproducibility Index

Core diagnostic scripts:

1. `python3.12 research/workspace/simulations/foundation_action_reduction_unification_check.py`
2. `python3.12 research/workspace/simulations/claim1_multimode_quartic_dereg_eta0_check.py`
3. `python3.12 research/workspace/simulations/claim1_multimode_quartic_nonperturbative_oscillatory_check.py`
4. `python3.12 research/workspace/simulations/claim6_schwarzschild_interval_scan.py`
5. `python3.12 research/workspace/simulations/claim3_coulomb_classification_scan.py`
6. `python3.12 research/workspace/simulations/claim1_groupoid_tau_sd_dependency_check.py`

## 11. Next Formal Target

Finish the current foundations-facing closure loop by (i) wiring the concrete exhaustion/regularization envelopes into the AN-33L-C commuting-limit wrapper on the field side (so the Lean wrapper can be invoked without hidden hypotheses), and (ii) continuing the Newton-limit paradox support lane (kernel-level \(t^{-d/2}\) semigroup normalization and Van Vleck/Schur prefactor links).

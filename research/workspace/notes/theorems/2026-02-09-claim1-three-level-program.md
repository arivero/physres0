# Claim 1 Phase AM: Three-Level Program with Dimension-Dependent Field Existence

Date: 2026-02-09 (CET)  
Primary anchors: `conv_patched.md:657`, `conv_patched.md:733`, `conv_patched.md:1132`, `conv_patched.md:1191`

## Goal

Lock Goal 1 into three explicit levels and separate:

1. what is proved in the current scoped program,
2. what remains open,
3. where existence is dimension-dependent at the field level.

Terminology guardrail:
use probability/transition amplitude language by default, reserve geometric \(1/2\)-density language for explicit kernel-bundle statements, and apply the skepticism protocol in `research/workspace/notes/2026-02-09-wikipedia-baseline-definitions-and-skepticism.md`.

## Level 0: Statics (Zero-Dimensional Action)

Prototype object:
\[
\delta(f'(x)).
\]
Nondegenerate critical-point decomposition:
\[
\delta(f'(x))=\sum_{x_i\in\mathrm{Crit}(f)}\frac{\delta(x-x_i)}{|f''(x_i)|}.
\]

`oscillatory amplitude` branch:
\[
A_\varepsilon(O)=\varepsilon^{-1/2}\int e^{\frac{i}{\varepsilon}f(x)}O(x)\,dx,
\qquad
|A_\varepsilon(O)|^2\to 2\pi\langle\delta(f'),|O|^2\rangle
\]
in the stationary-phase/nondegenerate regime.

Status in workspace: theorem-grade in scoped finite-dimensional classes
(distributional/static and manifold geometric \(1/2\)-density bridges).

## Level 1: Dynamics (0+1D Action on Time Histories)

Action:
\[
S[q]=\int_{t_i}^{t_f}L(q,\dot q,t)\,dt.
\]
Variational localization target:
\[
\delta\!\left(\frac{\delta S}{\delta q}\right).
\]
Time slicing gives finite-dimensional truncations, then controlled refinement.

Current Claim 1 closure here: strong scoped closure via projective/cylinder
families, de-regularization \(\eta\to0^+\), SD identities, and \(c\)-invariant
\(\tau_\mu\)-flow covariance.

Amplitude/geometry packaging choice:

1. with geometric \(1/2\)-density language: amplitude-first kernel composition (groupoid-aligned),
2. without geometric \(1/2\)-density language: work directly with normalized density/correlation functionals.

Both are admissible in the scoped program; geometric \(1/2\)-density packaging is structural, not mandatory.

## Level 2: Fields (d-Dimensional Spacetime Action)

Field action:
\[
S[\Phi]=\int_{\mathbb{R}^d}\mathcal{L}(\Phi,\partial\Phi,\dots)\,d^dx.
\]
Formal localization object:
\[
\delta\!\left(\frac{\delta S}{\delta \Phi}\right).
\]

Here, existence/continuum statements are dimension-sensitive.

### Dimension-Dependent Existence Ladder (Programmatic)

This table is a planning map for theorem targets, not a claim of full closure.

| Spacetime dimension \(d\) | Typical status of continuum construction target | Claim 1 implication |
|---|---|---|
| \(d=2\) | strongest constructive control in many model classes | best first target for full field-level closure |
| \(d=3\) | substantial constructive control for superrenormalizable classes | second target after \(d=2\), with tighter assumptions |
| \(d=4\) | physically central but hardest regime; rigorous continuum existence is model-dependent/open in key interacting cases | keep as main conceptual target, but do not overstate theorem status |
| \(d>4\) | EFT/nonrenormalizable behavior typically dominates generic local interactions | treat as asymptotic/EFT branch, not first closure target |

### Field-Level Amplitude / Geometric \(1/2\)-Density Branching

1. Kinematic geometric \(1/2\)-density branch:
   use amplitude/kernels with square-root Jacobian behavior under composition.
2. Correlator-only branch:
   avoid explicit geometric \(1/2\)-density formalism and work with Schwinger functions/Wightman-type objects plus reconstruction conditions.

Both branches must pass the same continuum-existence gate, which is \(d\)-dependent.

## Immediate Consequence for the Audit Queue

Next Claim 1 upgrade should be dimension-indexed:

1. close one non-Gaussian interacting field-limit theorem in \(d=2\) or \(d=3\),
2. explicitly document why the same proof does not automatically lift to \(d=4\),
3. keep \(d=4\) as the long-horizon frontier with explicit open assumptions.

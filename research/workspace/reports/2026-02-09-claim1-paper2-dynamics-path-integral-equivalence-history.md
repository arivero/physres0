# Paper 2: Dynamic Variational Consistency and Scoped Path-Integral Equivalence

Date: 2026-02-09

## Working Title

Dynamic Variational Consistency and Scoped Equivalence to the Path Integral (with Historical Discussion)

## Abstract

This paper develops a dynamic consistency chain for \(0+1\)-dimensional
actions: time-sliced transition amplitudes induce normalized cylinder states
that are stable under refinement, admit \(\eta\to0^+\) de-regularization,
satisfy Schwinger-Dyson identities, and are invariant under the \(c\)-preserving
flow \(\tau_\mu\). Under explicit assumptions, these statements imply scoped
equivalence to the path-integral formalism for the same model class and
boundary data. A dedicated historical section records the Dirac (1933) ->
Feynman (1948) -> Wilson-Kogut (1974) lineage.

## Scope

In-scope claim:

1. construction of a consistent continuum cylinder state from time slicing,
2. persistence of Schwinger-Dyson structure in the limit,
3. invariance along \(c\)-preserving reparameterizations,
4. identification of that limit with the path-integral functional in the same scoped class.

Out of scope:

1. full interacting field-theory closure in \(d=4\),
2. model-independent nonperturbative global path-integral existence,
3. scattering/unitarity claims beyond the scoped construction.

## Dynamic Setup

Let
\[
S[q]=\int_{t_i}^{t_f}L(q,\dot q,t)\,dt.
\]
At time-slicing resolution \(N\), write the discretized action \(S_N\) and define
\(x_0,x_N\) fixed boundary data with \(N-1\) interior integrations:
\[
\mathcal A_{\varepsilon,\varepsilon_0,N}(O)
:=
\int_{\mathbb R^{N-1}} \varepsilon^{-(N-1)/2}
\exp\!\left(\frac{i}{\varepsilon}\varepsilon_0\sum_{k=0}^{N-1}L_{\varepsilon_0}\!\left[x_k,\frac{x_{k+1}-x_k}{\varepsilon_0}\right]\right)
O[x_\bullet]\prod_{k=1}^{N-1}dx_k.
\]

For normalized states in the dressed notation:
\[
\omega_{c,N}(F):=
\frac{\int_{\mathbb R^N}e^{-cS_N(x)}F(x)\,dx}
{\int_{\mathbb R^N}e^{-cS_N(x)}\,dx},
\qquad c=(\eta-i/h)\kappa,\quad \Re c>0.
\]

## Dynamic Consistency Theorem Chain

Assume:

1. projective compatibility of cylinder observables under refinement,
2. denominator non-vanishing uniformly on compact \(c\)-domains,
3. uniform Cauchy-tail control for cylinder expectations,
4. finite-\(N\) Schwinger-Dyson identity,
5. \(c\)-invariance along \(\tau_\mu\)-orbits,
6. de-regularization \(\eta\to0^+\) pass-through in the scoped observable class.

Then the scoped chain gives:

1. convergence \(\omega_{c,N}(F_m)\to\omega_c(F_m)\),
2. invariance of \(\omega_c\) along \(\tau_\mu\)-orbits,
3. Schwinger-Dyson identities in the limit,
4. existence of the de-regularized state \(\omega_{-i\kappa/h}\) in scope (fixed \(\kappa\)).

Under these assumptions, the refinement limit of the normalized time-sliced
transition-amplitude channel equals \(\omega_c\) on the scoped cylinder class.

## Historical Discussion

1. **Dirac (1933):** exponential phase weighting and transition viewpoint.
2. **Feynman (1948):** time slicing and action-phase summation over histories.
3. **Wilson-Kogut (1974):** refinement as scale-control/RG problem.
4. **Current theoretical framing:** transition-amplitude composition plus explicit
   convergence gates and \(c\)-invariant SD structure, with geometric
   \(1/2\)-density language reserved for kernel-level structure.

## Validation Contract

1. **Assumptions:** model class, boundary data, regulator net, observable class,
   and normalization domain are explicit.
2. **Units/dimensions:** each action term has action units; \(S/\varepsilon\) is
   dimensionless; normalization factors tracked at each \(N\).
3. **Symmetry/conservation:** boundary-condition consistency, discrete variational
   identities, and conservation checks in scoped channels.
4. **Independent checks:**
   - analytic finite-dimensional SD and scale-flow covariance derivation channels,
   - numerical diagnostics:
     - `python3.12 research/workspace/simulations/claim1_cylinder_gaussian_toy.py`,
     - `python3.12 research/workspace/simulations/claim1_continuum_cauchy_diagnostics.py`,
     - `python3.12 research/workspace/simulations/claim1_fd_schwinger_dyson_check.py`,
     - `python3.12 research/workspace/simulations/claim1_scale_flow_covariance_check.py`,
     - `python3.12 research/workspace/simulations/claim1_groupoid_tau_sd_dependency_check.py`,
   - optional formal-companion modules:
     - `research/workspace/proofs/Claim1lean/CovarianceDerivative.lean`,
     - `research/workspace/proofs/Claim1lean/RatioStateDerivativeBound.lean`,
     - `research/workspace/proofs/Claim1lean/RatioStateIncrementBound.lean`,
     - `research/workspace/proofs/Claim1lean/FiniteExponentialIncrementBound.lean`,
     - `research/workspace/proofs/Claim1lean/FiniteExponentialRegularity.lean`.
5. **Confidence statement:** theorem-grade only within stated scoped assumptions.

## Reproducibility Metadata

1. TeX engine tested in this workspace: `/Library/TeX/texbin/pdflatex` (TeX Live 2025),
2. safe build script: `~/.codex/skills/pdflatex-safe-build/scripts/build_pdflatex_safe.sh`,
3. date anchor: 2026-02-09 (US).

## Conclusion

Dynamic variational consistency is presented as a self-contained theorem chain:
refinement stability, denominator control, SD persistence, and de-regularization
control. Within those assumptions, scoped equivalence to the path-integral
formalism is explicit and historically motivated.

# Foundational Glossary (Working)

Date: 2026-02-09

## Core Terms

`c-parameter`  
In the dressed kernel family,  
\[
c := (\eta - i/h)\kappa.
\]
Many identities are expressed only through this combined complex parameter.

`c-invariant`  
A quantity or statement is `c-invariant` if it is unchanged whenever parameters
\((\kappa,\eta,h)\) are changed in a way that keeps \(c\) fixed.
Equivalent phrasing: it is constant along a \(\tau_\mu\)-orbit.

`\tau_\mu` flow  
Scale reparameterization
\[
\tau_\mu:(\kappa,\eta,h)\mapsto(\mu\kappa,\eta/\mu,\mu h),\qquad \mu>0,
\]
which preserves \(c\).

`dressed kernel/state`  
The normalized oscillatory functional built from \(e^{-cS}\), after
regularization/normalization choices are fixed.

`de-regularization` (\(\eta\to0^+\))  
Passage from damped oscillatory weight \(e^{-(\eta-i/\varepsilon)S}\) to
the purely oscillatory branch by taking the one-sided limit \(\eta\downarrow 0\).

`Schwinger-Dyson (SD) identity`  
Integration-by-parts identity (finite-dimensional scoped form):
\[
\langle \partial_i\psi\rangle_c = c\,\langle \psi\,\partial_i S\rangle_c.
\]
In this workspace, SD identities are tracked as structure preserved under
\(\tau_\mu\) because they depend on \(c\).

`probability amplitude`  
Complex quantity whose modulus-square yields Born probabilities (physics-facing term).

`transition amplitude`  
Amplitude kernel between boundary data/time slices (dynamics/path-integral-facing term).

`half-density` / `1/2-density` (geometric term)  
Section of a square-root density bundle used in coordinate-free kernel composition.
In this workspace, reserve this term for explicit geometric kernel calculus.

`half-form` (geometric quantization term)  
Square-root bundle correction (metaplectic correction context), distinct from generic physics amplitude wording.

`terminology skepticism rule`  
Wikipedia definitions are orientation only. Theorem-grade claims require non-Wikipedia technical validation.

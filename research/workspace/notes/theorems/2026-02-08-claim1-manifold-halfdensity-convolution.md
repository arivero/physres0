# Claim 1 Step: Finite-Dimensional Manifold Half-Density Convolution Statement

Date: 2026-02-08  
Source anchors in canonical transcript: `conv_patched.md:814`, `conv_patched.md:928`, `conv_patched.md:967`

## Goal

State a finite-dimensional manifold result that is stronger than the flat static case and serves as the pre-infinite-dimensional bridge:

1. kernels as half-densities on a pair/tangent-groupoid setting,
2. coordinate-free convolution,
3. stationary-phase concentration on critical sets.

## Setup

Let \(M\) be a smooth \(n\)-dimensional manifold (with auxiliary Riemannian density for explicit formulas).  
On the pair groupoid \(G=M\times M\rightrightarrows M\), arrows are \((x,y)\), with composition
\[
(x,y)\circ(y,z)=(x,z).
\]

Half-density kernels are sections of
\[
\Omega^{1/2}_{s}\otimes\Omega^{1/2}_{t}
\]
on \(G\), where \(s,t\) are source/target maps.

## Proposition 1 (Coordinate-Free Convolution)

If \(K_1,K_2\) are compactly supported smooth half-density kernels on \(G\), then
\[
(K_1*K_2)(x,z)=\int_M K_1(x,y)\,K_2(y,z)
\]
is globally well-defined (coordinate-invariant) and defines again a smooth half-density kernel.

Interpretation: half-density normalization is exactly what removes coordinate Jacobian ambiguities in kernel composition.

## Oscillatory Family Near the Diagonal

Let \(f\in C^\infty(M)\) and choose a near-diagonal cutoff \(\chi\). Define
\[
K_\varepsilon^f(x,y)
=
\varepsilon^{-n/2}
\exp\!\left(\frac{i}{\varepsilon}(f(y)-f(x))\right)\chi(x,y)\,a_\varepsilon(x,y),
\]
with smooth amplitude \(a_\varepsilon\sim a_0+O(\varepsilon)\) as \(\varepsilon\to0^+\).

This is the manifold version of the ``near diagonal'' scaling used in the transcript.

## Proposition 2 (Local Stationary Concentration on Critical Set)

Assume \(f\) is Morse and let \(\psi\) be a compactly supported test half-density on \(M\).  
Define amplitude functional
\[
A_\varepsilon(\psi)
:=
\varepsilon^{-n/2}\int_M e^{\frac{i}{\varepsilon}f(x)}\psi(x).
\]

If \(f\) has a unique nondegenerate critical point \(x_0\) in \(\operatorname{supp}\psi\), then
\[
|A_\varepsilon(\psi)|^2
\to
(2\pi)^n
\frac{|\psi(x_0)|^2}{|\det(\operatorname{Hess}f)_{x_0}|}.
\]
Equivalently,
\[
|A_\varepsilon|^2
\to
(2\pi)^n\langle \delta(df), |\psi|^2\rangle
\]
in the single-point Morse case.

## Corollary (Finite-Dimensional Bridge Statement)

At finite dimension:

1. ``halved expression'' is naturally a half-density-level amplitude.
2. Modulus square yields a density-level concentration on critical sets.
3. The pair-groupoid convolution is already coordinate-free, matching the geometric interpretation in `conv_patched.md:814` and `conv_patched.md:967`.

This is the precise pre-infinite-dimensional step before attempting full path-space/groupoid continuum limits.

## Remaining Gap to Full Claim 1

Still open:

1. cylinder/projective limit control for \(N\to\infty\) (QM/QFT),
2. renormalization-compatible infinite-dimensional topology,
3. representation-level equivalence between tangent-groupoid convolution families and continuum quantum propagators.

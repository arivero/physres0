# Claim 1 Phase C: Pair/Tangent-Groupoid Half-Density Theorem Pack

Date: 2026-02-08  
Source anchors in canonical transcript: `conv_patched.md:814`, `conv_patched.md:928`, `conv_patched.md:967`

## Goal

Promote the finite-dimensional groupoid step to explicit theorem/proof format with clear hypotheses, convolution laws, and \(\varepsilon\to0\) composition structure.

## Hypotheses

Let \(M\) be a smooth \(n\)-manifold with positive smooth density \(\nu\).  
On pair groupoid \(G=M\times M\rightrightarrows M\), use half-density kernels
\[
K\in C_c^\infty\!\big(G,\Omega_s^{1/2}\otimes\Omega_t^{1/2}\big).
\]
Locally,
\[
K(x,y)=k(x,y)\,|\nu_x|^{1/2}|\nu_y|^{1/2}.
\]

## Theorem 1 (Convolution Well-Defined and Coordinate-Free)

Define
\[
(K_1*K_2)(x,z)
:=
\int_M k_1(x,y)k_2(y,z)\,\nu(y)\,|\nu_x|^{1/2}|\nu_z|^{1/2}.
\]
Then \(K_1*K_2\) is again a compactly supported smooth half-density kernel, independent of local coordinate choices.

### Proof sketch

Half-density factors absorb Jacobians from coordinate changes on \(y\), leaving scalar integral invariant. Smoothness/compact support follow from standard pushforward under proper support.

## Theorem 2 (Associativity and Involution)

With involution
\[
K^\ast(x,y):=\overline{K(y,x)},
\]
the algebra satisfies:

1. \((K_1*K_2)*K_3=K_1*(K_2*K_3)\),
2. \((K_1*K_2)^\ast=K_2^\ast*K_1^\ast\).

### Proof sketch

Associativity is Fubini/Tonelli on iterated \(y,z\) integrals under compact support; involution is direct conjugation/swap under integral.

## Tangent-Groupoid Family

For Connes tangent groupoid:
\[
\mathbb T M=(M\times M\times(0,1])\sqcup (TM\times\{0\}),
\]
composition is pair-groupoid composition for \(\varepsilon>0\), and fiberwise vector addition for \(\varepsilon=0\).

## Theorem 3 (Scaled Family Composition Law)

Let \(K_\varepsilon\) be an admissible scaled family with near-diagonal structure
\[
K_\varepsilon(x,y)\sim \varepsilon^{-n/2}e^{\frac{i}{\varepsilon}\Phi(x,y)}a_\varepsilon(x,y),
\]
and symbol bounds ensuring uniform proper support and stationary-phase control. Then:

1. for each \(\varepsilon>0\), \(K_\varepsilon\) composes by pair-groupoid convolution;
2. principal \(\varepsilon\to0\) limit is a fiberwise convolution law on \(TM\) (Fourier-dual symbol product).

This is the formal geometric mechanism behind the ``near diagonal'' Claim 1 interpretation.

## Corollary

At finite dimension, half-density amplitudes and their compositions are algebraically controlled before any infinite-dimensional limit is invoked.  
This isolates the true open frontier to continuum-limit and renormalization questions, not to the local groupoid algebra itself.

## Reproducibility Check

Run:

```bash
python3.12 research/workspace/simulations/claim1_pair_groupoid_convolution_check.py
```

This verifies weighted discrete analogues of associativity and involution identities.

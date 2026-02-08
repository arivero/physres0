# Claim 4 Formalization: \(n=3\) Duffing Reduction and Phase Portrait

Date: 2026-02-08  
Source anchors in canonical transcript: `conv_patched.md:426`, `conv_patched.md:434`, `conv_patched.md:436`

## Goal

Formalize the \(n=3\) orbit equation as a Hamiltonian Duffing-type system and extract precise statements about instability, center access, and nongeneric bounded behavior.

## Reduced Equation

For \(n=3\), the transcript gives
\[
u''+\left(1-\frac{KE}{c^2L^2}\right)u
=
\frac{K^2}{2c^2L^2}u^3.
\]
Write
\[
a:=1-\frac{KE}{c^2L^2},\qquad
b:=\frac{K^2}{2c^2L^2}>0.
\]
Then
\[
u''=-a\,u+b\,u^3.
\]

Physical sector for orbital radius is \(u=1/r>0\).

## First Integral

Define
\[
W(u):=\frac{a}{2}u^2-\frac{b}{4}u^4,\qquad
H:=\frac12 (u')^2+W(u).
\]
Direct differentiation gives \(H'=0\), so \(H\) is conserved.

## Proposition 1 (Equilibria and Circular Orbit Instability)

Equilibria satisfy \(u'=0\) and \(-au+bu^3=0\):

1. \(u=0\) always.
2. If \(a>0\), also \(u_\star=\sqrt{a/b}\) (and \(-u_\star\) on full line).

In the physical branch \(u>0\), \(u_\star\) corresponds to the finite-radius circular orbit.

Linearizing \(u=u_\star+\eta\):
\[
\eta''=(-a+3bu_\star^2)\eta = 2a\,\eta.
\]
Hence for \(a>0\), perturbations grow/decay exponentially in \(\varphi\), so the circular orbit is linearly unstable.

## Proposition 2 (No Angular-Momentum Exclusion of the Center)

For \(n=3\), \(V(r)=-K/(2r^2)\). In radial momentum form:
\[
p_r^2(r)=\frac{(E-V(r))^2-m^2c^4}{c^2}-\frac{L^2}{r^2}.
\]
As \(r\to 0^+\):
\[
\frac{(E-V)^2}{c^2}\sim \frac{K^2}{4c^2}\frac1{r^4},
\qquad
\frac{L^2}{r^2}\sim \frac{L^2}{r^2}.
\]
Since \(r^{-4}\) dominates \(r^{-2}\),
\[
p_r^2(r)\to +\infty.
\]
Therefore finite \(L\) does not kinematically forbid approach to \(r=0\) (plunge remains allowed).

## Proposition 3 (Phase-Space Structure on \(u>0\))

Assume \(a>0\). Then \(W\) has one positive local maximum at \(u_\star\):
\[
W_{\max}=W(u_\star)=\frac{a^2}{4b}.
\]

For any fixed energy level \(H\):

1. The only compact invariant set in \(u>0\) is the equilibrium \(u=u_\star\) (circular orbit).
2. Non-equilibrium trajectories either:
   - cross toward \(u\to 0^+\) (corresponding to \(r\to\infty\), escape branch), or
   - move to large \(u\) (corresponding to \(r\to 0\), plunge branch).

Sketch: \(W(u)\to -\infty\) as \(u\to\infty\), so every energy level intersects an unbounded-\(u\) region. Near \(u_\star\), the linearization is hyperbolic, so no open neighborhood of bounded non-circular motion exists in \(u>0\).

## Corollary (Claim 4 Upgrade)

Within this reduced \(n=3\) SR model:

- circular finite-radius motion is a measure-zero tuning (single equilibrium in the \((u,u')\) phase plane);
- it is unstable;
- finite \(L\) does not create a strict centrifugal exclusion of \(r=0\);
- thus generic perturbations follow escape/plunge branches, consistent with `conv_patched.md:434` and `conv_patched.md:436`.

## Reproducibility Check (Numerical Sanity)

Run:

```bash
python3.12 research/workspace/simulations/claim4_duffing_n3_portrait_check.py
```

This check numerically verifies local instability of \(u_\star\) and branch splitting under small perturbations.

## Companion Global-Time Note

See:

`research/workspace/notes/theorems/2026-02-08-claim4-n3-global-time-classification.md`

for coordinate-time turning-set topology in \(r\) (escape/plunge channel structure and absence of generic bounded shell).

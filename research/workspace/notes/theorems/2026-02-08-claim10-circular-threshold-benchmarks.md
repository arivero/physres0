# Claim 10 Formalization: Circular-Orbit Threshold Benchmarks

Date: 2026-02-08  
Source anchors in canonical transcript: `conv_patched.md:143`, `conv_patched.md:230`

## Goal

Provide model-internal benchmark derivations for two circular-orbit threshold statements:

1. \(n=2:\; L > K/c\).
2. \(n=3:\; L^2 \ge K m\) (strict \(>\) for finite-radius motion).

These are used as invariant checks for later extensions.

## Common Setup

Assume special-relativistic planar circular motion in an attractive central force of magnitude
\[
F(r)=\frac{K}{r^n},\qquad K>0.
\]

For circular motion with speed \(v\) and radius \(r\):
\[
\frac{K}{r^n}= \gamma m \frac{v^2}{r},
\qquad
\gamma=\frac{1}{\sqrt{1-v^2/c^2}},
\qquad
L=\gamma m v r.
\]

The only physical constraint used is \(0\le v < c\), equivalently \(\gamma\ge 1\).

## Proposition 1 (\(n=2\): Kepler/Coulomb Threshold)

For \(F=K/r^2\), every finite-radius circular orbit satisfies
\[
L>\frac{K}{c}.
\]

### Proof

At \(n=2\),
\[
\frac{K}{r^2}=\gamma m\frac{v^2}{r}
\;\Longrightarrow\;
K=\gamma m v^2 r.
\]
Using \(L=\gamma m v r\),
\[
\frac{K}{L}
=
\frac{\gamma m v^2 r}{\gamma m v r}
=
v.
\]
Hence \(v=K/L\). Physical admissibility \(v<c\) gives
\[
\frac{K}{L}<c
\;\Longrightarrow\;
L>\frac{K}{c}.
\]
At \(L\downarrow K/c\), one has \(v\uparrow c\), so equality is a limiting non-regular endpoint, not a finite-radius timelike circular orbit.

## Proposition 2 (\(n=3\): Inverse-Cubic Threshold)

For \(F=K/r^3\), every circular orbit satisfies
\[
L^2\ge Km,
\]
with equality corresponding to \(v=0\) and \(r\to\infty\). Thus finite-radius circular motion requires
\[
L>\sqrt{Km}.
\]

### Proof

At \(n=3\),
\[
\frac{K}{r^3}=\gamma m\frac{v^2}{r}
\;\Longrightarrow\;
\frac{K}{r^2}=\gamma m v^2.
\]
Multiply by \(r^2\):
\[
K=\gamma m v^2 r^2.
\]
From \(L=\gamma m v r\), we have
\[
L^2=\gamma^2 m^2 v^2 r^2
=
\gamma m\left(\gamma m v^2 r^2\right)
=
\gamma m K.
\]
Therefore
\[
L^2=Km\,\gamma\ge Km.
\]
Equality means \(\gamma=1\Rightarrow v=0\); with finite \(K\), circular-balance equations then force \(r\to\infty\). Hence finite-radius circular orbits require strict inequality.

## Corollary (Benchmark Status)

Both Claim 10 inequalities are direct algebraic consequences of the SR circular-orbit equations in the stated model and are suitable as baseline checks for any generalized framework.

# Claim 1 Deepening: Discrete Variational-Delta Lemmas for QM and Lattice QFT

Date: 2026-02-08  
Source anchors in canonical transcript: `conv_patched.md:1068`, `conv_patched.md:1088`, `conv_patched.md:1132`, `conv_patched.md:1152`

## Goal

Make the finite-dimensional truncation step explicit:
\[
\delta\!\left(\frac{\delta S}{\delta\text{field}}\right)
\rightsquigarrow
\delta(\nabla S_N),
\]
with exact support/weight formulas at fixed discretization size \(N\).

## Lemma 1 (Multivariate Delta of a Gradient Map)

Let \(S_N:\mathbb{R}^N\to\mathbb{R}\) be smooth with isolated nondegenerate critical points
\[
\nabla S_N(x_i)=0,\qquad \det H_i\neq 0,\quad H_i:=\nabla^2 S_N(x_i).
\]
Then distributionally
\[
\delta(\nabla S_N(x))
=
\sum_i \frac{\delta(x-x_i)}{|\det H_i|}.
\]

Hence for test \(g\):
\[
\langle \delta(\nabla S_N),g\rangle
=
\sum_i \frac{g(x_i)}{|\det H_i|}.
\]

## Lemma 2 (Discrete Mechanics Support Statement)

Let a time-sliced mechanical action
\[
S_N(q_1,\dots,q_{N-1})
=
\sum_{k=0}^{N-1} L_d(q_k,q_{k+1};\Delta t),
\]
with fixed endpoints \(q_0,q_N\). Then
\[
\nabla S_N = 0
\]
is exactly the discrete Euler--Lagrange system:
\[
D_2 L_d(q_{k-1},q_k;\Delta t)+D_1 L_d(q_k,q_{k+1};\Delta t)=0.
\]
Therefore \(\delta(\nabla S_N)\) is concentrated on discrete classical trajectories.

## Lemma 3 (Lattice Field-Theory Support Statement)

For lattice field variables \(\Phi=(\Phi_1,\dots,\Phi_N)\) and action \(S_N(\Phi)\), the stationarity equations are
\[
\frac{\partial S_N}{\partial \Phi_a}=0,\qquad a=1,\dots,N.
\]
Hence
\[
\delta(\nabla S_N(\Phi))
\]
is a Dirac measure concentrated on lattice classical field configurations.

## Proposition (Finite-\(N\) Halved-Amplitude Squared Limit)

Define finite-\(N\) oscillatory amplitude
\[
A_{\varepsilon,N}(O)
:=
\varepsilon^{-N/2}\int_{\mathbb{R}^N}
e^{\frac{i}{\varepsilon}S_N(x)}\,O(x)\,dx.
\]
Under a single nondegenerate critical point \(x_\star\),
\[
|A_{\varepsilon,N}(O)|^2
=
(2\pi)^N\frac{|O(x_\star)|^2}{|\det H_\star|}
+o(1),
\qquad \varepsilon\to 0^+.
\]
Equivalently
\[
|A_{\varepsilon,N}(O)|^2
\to
(2\pi)^N\langle \delta(\nabla S_N), |O|^2\rangle.
\]

## Corollary (Claim 1 Ladder Strengthening)

At every fixed discretization level:

1. static case (\(N\)-dimensional finite action),
2. QM time-sliced action,
3. lattice QFT action,

the ``delta of first variation selects extrema'' statement is exact and theorem-level.  
The remaining nontrivial step is the \(N\to\infty\) continuum/renormalized limit.

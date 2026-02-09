# Claim 1 Phase B: Controlled Cylinder-Limit Program (QM and Lattice QFT)

Date: 2026-02-08  
Source anchors in canonical transcript: `conv_patched.md:1068`, `conv_patched.md:1096`, `conv_patched.md:1132`, `conv_patched.md:1152`, `conv_patched.md:1166`

## Goal

Specify a concrete finite-to-infinite program for the Claim 1 bridge:

1. define compatible finite-dimensional truncations,
2. state convergence assumptions explicitly,
3. separate successful vs failing truncation patterns.

## Truncation Framework

Let \(X_N=\mathbb R^N\) with projections \(\pi_{N+1\to N}\).  
At scale \(N\), define action \(S_N\) and oscillatory functional
\[
\mathcal A_{\varepsilon,N}(O_N)
:=
\int_{X_N} e^{\frac{i}{\varepsilon}S_N(x)}\,O_N(x)\,dx.
\]

Use normalized expectations
\[
\mathbb E_{\varepsilon,N}[O_N]
:=
\frac{\mathcal A_{\varepsilon,N}(O_N)}
{\mathcal A_{\varepsilon,N}(1)}.
\]

For a cylinder observable \(O_N=O_m\circ\pi_{N\to m}\) (\(N\ge m\)), the target is stabilization in \(N\).

## Assumption Package

### A1 (Projective Compatibility)

\[
S_{N+1}(x,\xi)=S_N(x)+\Delta S_{N+1}(x,\xi),
\]
with \(\Delta S_{N+1}\) depending on the new block \(\xi\) in a way compatible with \(\pi_{N+1\to N}\) (exact factorization or controlled perturbative correction).

### A2 (Uniform Nondegenerate Stationary Control)

Critical sets and Hessian determinants for \(S_N\) satisfy bounds uniform enough in \(N\) to prevent prefactor blow-up for normalized expectations.

### A3 (Renormalization/Counterterm Compatibility)

If raw \(S_N\) violates A2, introduce \(S_N^{\mathrm{ren}}\) by \(N\)-dependent counterterms/couplings so that A1+A2 hold for the renormalized family.

### A4 (Observable Class Control)

Restrict to cylinder observables (or dense generated class) with explicit growth/integrability bounds; non-cylinder observables are treated separately and may fail to converge.

## Program Statement

Under A1--A4:

1. \(\mathbb E_{\varepsilon,N}[O_m\circ\pi_{N\to m}]\) stabilizes as \(N\to\infty\) (or converges in a controlled topology).
2. The resulting limit functional is the candidate continuum object at fixed \(\varepsilon\).
3. The subsequent \(\varepsilon\to 0\) step is taken after \(N\to\infty\), with channel tracking from Phase A.

## Failure Modes (Explicit)

1. **Incompatible truncation family**: \(S_N\) not projectively coherent (different physics across \(N\)).
2. **Uncontrolled Hessian growth/degeneracy**: oscillatory prefactors drift/diverge.
3. **No renormalized coupling flow**: normalization ratios fail to stabilize.
4. **Observable mismatch**: non-cylinder observables probe UV directions with no projective limit.

## Toy Model (Exact Cylinder Success + Explicit Failure)

The script below gives:

1. exact \(N\)-independence for a compatible Gaussian cylinder family;
2. oscillatory non-convergence for an intentionally incompatible alternating family.

Run:

```bash
python3.12 research/workspace/simulations/claim1_cylinder_gaussian_toy.py
```

## Corollary

Claim 1 now has a concrete continuum roadmap:

1. finite-dimensional variational-delta statements,
2. finite-dimensional manifold geometric \(1/2\)-density kernel algebra,
3. controlled cylinder-limit requirements and diagnostics,

leaving only the full renormalized continuum bridge as the remaining speculative frontier.

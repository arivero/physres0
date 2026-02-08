# Claim 1 Scoping: Half-Density and Tangent-Groupoid Bridge

Date: 2026-02-08  
Source anchors in canonical transcript: `conv_patched.md:814`, `conv_patched.md:934`, `conv_patched.md:967`, `conv_patched.md:991`

## Purpose

Reduce Claim 1 from a broad speculative statement into:

1. a theorem-level static statement (0-dimensional oscillatory integral), and
2. a precise conjectural bridge statement for the full path-integral/groupoid setting.

## Level A (Theorem-Grade Static Core)

Let \(f\in C^\infty(\mathbb{R})\) have a unique nondegenerate critical point \(x_0\),
\[
f'(x_0)=0,\qquad f''(x_0)\neq 0,
\]
and let \(O\in C_c^\infty(\mathbb{R})\). Define
\[
A_\varepsilon(O):=\varepsilon^{-1/2}\int_{\mathbb{R}} e^{\frac{i}{\varepsilon}f(x)}\,O(x)\,dx,\qquad \varepsilon>0.
\]

Then stationary phase yields
\[
|A_\varepsilon(O)|^2
=
2\pi\frac{|O(x_0)|^2}{|f''(x_0)|}
+o(1)
\quad(\varepsilon\to 0^+),
\]
up to normalization convention in Fourier transform constants.

Equivalent distributional form (single-point Morse case):
\[
|A_\varepsilon(O)|^2
\to
2\pi\langle \delta(f'), |O|^2\rangle.
\]

Interpretation: the \(\varepsilon^{-1/2}\) scaling is exactly the amplitude normalization that makes the modulus square converge to a density-level object supported on classical critical points.

### Multi-Critical Remark

If \(f\) has several nondegenerate critical points
\[
\mathrm{Crit}(f)=\{x_j\}_{j=1}^N,\qquad f'(x_j)=0,\quad f''(x_j)\neq 0,
\]
then \(A_\varepsilon\) is a sum of stationary-phase contributions with relative phases \(e^{i(f(x_i)-f(x_j))/\varepsilon}\). In general, pointwise limits of \(|A_\varepsilon|^2\) may fail to exist due to oscillatory cross terms; diagonal sums arise after additional averaging/weak-limit prescriptions.

## Level B (Geometric Reformulation Target)

Use the tangent-groupoid near-diagonal scaling \((x,y,\varepsilon)\) with \(y=x+\varepsilon z\), and represent kernels as half-densities so convolution is coordinate-free.

The concrete target statement is:

For an admissible kernel family \(K_\varepsilon\) built from phase increments
\[
K_\varepsilon(x,y)\sim \exp\!\left(\frac{i}{\varepsilon}(f(y)-f(x))\right),
\]
the induced half-density convolution algebra has a well-defined \(\varepsilon\to 0\) classical limit matching the critical-point measure above.

This identifies the "halved object" with a half-density-level amplitude whose square produces a density-level limit.

## Level C (Still Conjectural in Current Notes)

The full statement "this tangent-groupoid half-density construction yields the same object as the continuum Feynman path integral for interacting field theories" remains conjectural in this workspace.

Current gap items:

1. Domain/completion choices for oscillatory kernels in infinite dimensions.
2. Control of off-diagonal/interference terms in non-Morse or multi-branch settings.
3. Precise representation-theoretic map from groupoid convolution to continuum quantum propagators beyond formal asymptotics.

## Minimal Novelty Roadmap

1. Prove the static finite-dimensional statement in complete detail (already standard, but write self-contained proof with constants).
2. Extend to finite-dimensional manifold configuration spaces using half-densities and local charts.
3. Define an explicit cylinder-limit scheme where each truncation is a rigorous groupoid/half-density object and show compatibility of limits.

## Status Update for Claim 1

- Upgraded from broad speculation to a split status:
  - `proved (static core)`,
  - `speculative (full path-integral equivalence)`.
- This keeps novelty while making the technical frontier explicit and testable.

## Reproducibility Check (Static Core)

Run:

```bash
python3.12 research/workspace/simulations/claim1_halfdensity_static_check.py
```

The script uses an exactly solvable Gaussian test case and verifies
\[
|A_\varepsilon|^2 \to 2\pi
\]
as \(\varepsilon\to 0^+\), matching the static half-density scaling claim.

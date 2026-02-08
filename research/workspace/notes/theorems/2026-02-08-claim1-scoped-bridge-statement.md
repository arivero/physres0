# Claim 1 Scoping: Half-Density and Tangent-Groupoid Bridge

Date: 2026-02-08  
Source anchors in canonical transcript: `conv_patched.md:814`, `conv_patched.md:934`, `conv_patched.md:967`, `conv_patched.md:991`, `conv_patched.md:1068`, `conv_patched.md:1088`, `conv_patched.md:1132`, `conv_patched.md:1152`

## Purpose

Reduce Claim 1 from a broad speculative statement into:

1. a theorem-level static statement (0-dimensional oscillatory integral), and
2. a precise conjectural bridge statement for the full path-integral/groupoid setting.

## Variational-Delta Ladder (Static -> QM -> QFT)

Notation clarification used in these notes:

- We use `delta-of-derivative` (or `delta-of-first-variation`), e.g.
  \[
  \delta(f')\quad\text{or}\quad \delta\!\left(\frac{\delta S}{\delta \phi}\right),
  \]
  meaning a Dirac delta concentrated on extrema.
- More precisely, \(\delta(f')\) is a pullback/composition by the map \(f'\), not the distribution derivative \(\partial_x\delta\) (often denoted \(\delta'\)).
- Both objects belong the point-supported-distribution framework: in 1D, point-supported distributions are finite sums \(\sum_{m=0}^N c_m\,\delta^{(m)}\), with dilation weights \(\delta^{(m)}(\lambda x)\sim \lambda^{-m-1}\delta^{(m)}(x)\) (\(\lambda>0\)). This gives multiple scaling eigendirections/fixed-mode channels, not a single one.

The same extremum-selector pattern appears at three levels.

1. Static finite-dimensional level:
   \[
   S(x)=f(x),\qquad \Delta_{\text{stat}}:=\delta(\nabla S).
   \]
   For isolated nondegenerate critical points \(x_i\),
   \[
   \delta(\nabla S)=\sum_i \frac{\delta_{x_i}}{|\det \nabla^2 S(x_i)|}.
   \]

2. Quantum mechanics (time paths):
   \[
   S[\phi]=\int_{t_0}^{t_1}L(\phi,\dot\phi)\,dt,\qquad
   \Delta_{\text{QM}}:=\delta\!\left(\frac{\delta S}{\delta\phi}\right).
   \]
   Support is on Euler-Lagrange solutions \(\delta S/\delta\phi=0\).

3. Quantum field theory (spacetime fields):
   \[
   S[\Phi]=\int \mathcal{L}(\Phi,\partial\Phi)\,d^Dx,\qquad
   \Delta_{\text{QFT}}:=\delta\!\left(\frac{\delta S}{\delta\Phi}\right).
   \]
   Support is on classical field equations \(\delta S/\delta\Phi=0\).

Regularized finite-dimensional approximations make the parallel explicit:

- QM time slicing: \(\phi\mapsto (q_1,\dots,q_N)\), then \(\Delta_{\text{QM}}\) becomes \(\delta(\nabla S_N)\).
- Lattice QFT: \(\Phi\mapsto (\Phi_1,\dots,\Phi_N)\), then \(\Delta_{\text{QFT}}\) becomes \(\delta(\nabla S_N)\).

So the escalation static -> QM -> QFT preserves the same core interpretation: the delta object localizes on extrema of the corresponding action.

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
4. Continuum-limit control from finite-dimensional \(\delta(\nabla S_N)\) to functional \(\delta(\delta S)\) in QM/QFT (including renormalization in QFT).

## Minimal Novelty Roadmap

1. Prove the static finite-dimensional statement in complete detail (already standard, but write self-contained proof with constants).
2. Write finite-dimensional discrete-action lemmas (\(\delta(\nabla S_N)\) support on discrete Euler-Lagrange equations) for QM and lattice QFT.
3. Extend to finite-dimensional manifold configuration spaces using half-densities and local charts.
4. Define an explicit cylinder-limit scheme where each truncation is a rigorous groupoid/half-density object and show compatibility of limits.

## Status Update for Claim 1

- Upgraded from broad speculation to a split status:
  - `proved (static core)`,
  - `formal/heuristic (QM and QFT functional-delta interpretation)`,
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

## Companion Note (Discrete Truncations)

For finite-dimensional QM/lattice-QFT truncations, see:

`research/workspace/notes/theorems/2026-02-08-claim1-discrete-variational-delta-lemmas.md`

This makes \(\delta(\nabla S_N)\) support/weights explicit before continuum limits.

For the finite-dimensional manifold/groupoid half-density step, see:

`research/workspace/notes/theorems/2026-02-08-claim1-manifold-halfdensity-convolution.md`

For explicit multi-channel point-supported scaling modes, see:

`research/workspace/notes/theorems/2026-02-08-claim1-point-supported-scaling-channels.md`

For the controlled cylinder-limit program (QM/lattice-QFT truncations), see:

`research/workspace/notes/theorems/2026-02-08-claim1-cylinder-limit-program.md`

For theorem-format pair/tangent-groupoid half-density composition laws, see:

`research/workspace/notes/theorems/2026-02-08-claim1-groupoid-halfdensity-theorem-pack.md`

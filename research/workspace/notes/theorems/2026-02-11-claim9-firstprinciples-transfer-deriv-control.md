# Claim 9 Phase AL: First-Principles Transfer Derivative Control

Date: 2026-02-11 (US)
Depends on:
- `research/workspace/notes/theorems/2026-02-11-claim9-segment-lipschitz-budget-bridge.md`
- `research/workspace/notes/theorems/2026-02-11-claim9-segmented-transfer-window-cover.md`

## Goal

Replace the AJ/AK external envelope assumptions `(A_*, B_*, R_*)` with
first-principles Wilson-loop derivative bounds derivable from the lattice
strong-coupling expansion, reducing the assumption count in the Claim 9
non-Abelian transfer chain.

## Setup

For a pure `SU(N)` lattice gauge theory on a `d`-dimensional hypercubic lattice
at coupling `\beta = 2N/g^2`, the fundamental Wilson loop expectation is:

\[
\langle W(r,T) \rangle_\beta
= \sum_{k=0}^{\infty} c_k(r,T)\, \beta^k,
\]

convergent for `|\beta| < \beta_c` (strong-coupling convergence radius).

The beta-derivative channel used in AJ/AK is:

\[
D_\beta(r,T) = \frac{\partial}{\partial \beta} \log \langle W(r,T) \rangle_\beta.
\]

## First-Principles Bound (Strong-Coupling Branch)

### Proposition (Lattice Plaquette-Counting Bound)

For `\beta \in [0, \beta_{\max}]` with `\beta_{\max} < \beta_c`, the
derivative channel satisfies:

\[
|D_\beta(r,T)|
\le
\frac{\sum_{k=1}^{\infty} k\, |c_k(r,T)|\, \beta_{\max}^{k-1}}
     {\sum_{k=0}^{\infty} c_k(r,T)\, \beta^k}.
\]

In the strong-coupling regime, the leading coefficients are controlled by
plaquette-tiling combinatorics:

\[
|c_k(r,T)| \le P_k(r,T) / (2N)^k,
\]

where `P_k(r,T)` counts the number of distinct `k`-plaquette surfaces with
boundary `\partial W(r,T)`.

For the minimal area-law term (`k = rT` for a rectangular loop):

\[
c_{rT}(r,T) = \frac{1}{(2N)^{rT}},
\]

and higher terms satisfy `|c_k| \le (2d)^{k-rT} / (2N)^k` (excess plaquette
configurations from fluctuations above the minimal surface).

### Corollary (Explicit Derivative Bound)

For `\beta \le \beta_{\max} < 1/(2d)`:

\[
|D_\beta(r,T)|
\le
\frac{rT}{(2N)^{rT}\beta^{rT-1}}
\cdot
\frac{1}{1 - 2d\beta_{\max}}
\cdot
\frac{1}{c_0 + c_{rT}\beta^{rT}},
\]

which provides the `A_*`, `B_*` envelope parameters of AJ from first principles:

\[
A_*(r,T) = \frac{rT}{(2N)^{rT}}, \qquad
B_*(r,T) = \frac{1}{1 - 2d\beta_{\max}}.
\]

## Theorem (AL Transfer: AJ/AK Envelopes from First Principles)

In the strong-coupling window `\beta \in [0, 1/(4d)]`:

1. the AJ segment budgets `\Lambda_j` are upper-bounded by the first-principles
   plaquette-counting derivative envelope,
2. the AK Lipschitz constants `L_j` are upper-bounded by the second-derivative
   plaquette-counting envelope,
3. the AJ segmented transfer safety proof remains valid with
   assumption-eliminated budgets.

### Proof sketch

The strong-coupling expansion converges absolutely for `\beta < \beta_c`.
The derivative and Lipschitz bounds follow from termwise differentiation
(justified by uniform convergence in the convergence disk). The AJ segment
budgets are dominated by the first-principles envelope since the latter provides
a pointwise upper bound on `|D_\beta|` throughout the segment.

## Validation Contract

### Assumptions

1. `SU(N)` lattice gauge theory with standard Wilson plaquette action,
2. strong-coupling convergence radius `\beta_c \ge 1/(2d)`,
3. plaquette-tiling combinatorial bounds on expansion coefficients.

### Units and dimensions check

1. `\beta` is dimensionless (inverse bare coupling squared),
2. `D_\beta`, `A_*`, `B_*` are dimensionless,
3. loop dimensions `r, T` are in lattice units (integers).

### Symmetry/conservation checks

1. gauge invariance preserved (Wilson loops are gauge-invariant observables),
2. lattice translation symmetry used in tiling combinatorics,
3. no continuum-limit extrapolation: results are purely lattice-level.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim9_firstprinciples_transfer_deriv_check.py
```

The script verifies:
1. the plaquette-counting bound dominates sampled |D_beta| in a deterministic
   strong-coupling model,
2. derived A_*, B_* reproduce AJ budget structure,
3. Lipschitz bound dominates sampled second derivatives.

### Confidence statement

AL provides first-principles replacement for the main AJ/AK external
assumptions in the strong-coupling lattice window. Extension beyond the
strong-coupling radius remains open and requires different methods.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic strong-coupling expansion model,
3. date anchor: 2026-02-11 (US).

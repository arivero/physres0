# Claim 1 Support (Newton-Limit Paradox): Lean Schur-Complement Determinant Template

Date: 2026-02-10 (US)  
Lean module: `research/workspace/proofs/Claim1lean/SchurComplementDeterminant.lean`

## Goal

Record a machine-checked finite-dimensional algebraic backbone for the
“Gaussian elimination / integrate-out intermediate variables” template:

1. Schur complement controls the reduced quadratic form after eliminating a block,
2. determinant factorization produces the corresponding prefactor.

This is the determinant-side core of the Van Vleck / mixed-Hessian prefactor lane.

## Machine-Checked Statements (Lean)

In `Claim1lean.Schur`, we define (for block matrices `[A B; C D]`):

- `complement₁₁(A,B,C,D) = D - C * ⅟A * B` (requires `[Invertible A]`),
- `complement₂₂(A,B,C,D) = A - B * ⅟D * C` (requires `[Invertible D]`).

Then we prove wrapper lemmas (directly delegating to mathlib):

1. `det_fromBlocks₁₁`:
   \[
   \det\begin{pmatrix}A & B\\ C & D\end{pmatrix}
   =
   \det(A)\,\det(D - C A^{-1} B).
   \]
2. `det_fromBlocks₂₂`:
   \[
   \det\begin{pmatrix}A & B\\ C & D\end{pmatrix}
   =
   \det(D)\,\det(A - B D^{-1} C).
   \]
3. `isUnit_fromBlocks_iff₁₁` and `isUnit_fromBlocks_iff₂₂`:
   invertibility of the block matrix is equivalent to invertibility of the corresponding
   Schur complement (under the stated invertibility assumption on the pivot block).

## Why This Matters Here

When a refined action splits into “kept variables” and “integrated-out variables” with
quadratic (Gaussian) structure, the reduced kernel/action typically involves:

1. a Schur-complement quadratic form,
2. a determinant prefactor from the elimination step.

This note provides the rigorous algebraic determinant side of that pattern (no analysis).
It is intended to be cited when connecting:

- semigroup/composition consistency,
- forced normalization and prefactors (`t^{-d/2}`, Van Vleck determinants),
- and the half-density/amplitude necessity framing in the Newton-limit paradox note.

## Next Tightening Targets

1. Add a “completion of squares” quadratic-form identity on block matrices (still algebraic),
   matching the Schur-complement reduction at the exponent level.
2. Use the algebraic elimination + a separate analytic Gaussian-integral lemma to finish the
   semigroup-normalization (`t^{-d/2}`) theorem lane. Current Lean anchor on the Gaussian side:
   `research/workspace/notes/theorems/2026-02-10-claim1-lean-gaussian-semigroup-normalization.md`.

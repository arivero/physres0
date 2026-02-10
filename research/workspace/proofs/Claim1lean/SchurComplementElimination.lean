import Claim1lean.SchurComplementDeterminant

/-!
Schur-complement elimination (LDU decomposition) template.

This packages mathlib's `Matrix.fromBlocks_eq_of_invertible₁₁` in the same naming/convention
layer used by `Claim1lean.SchurComplementDeterminant.lean`.

Interpretation (informal): for a 2×2 block matrix, left/right multiplication by block-unit
triangular matrices performs the algebraic elimination step corresponding to “complete the
square / integrate out intermediate variables”, producing a reduced block equal to the Schur
complement `D - C A^{-1} B`.

No integration is formalized here; this is purely algebraic.
-/

namespace Claim1lean

namespace Schur

open Matrix

section

variable {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable [CommRing α]

theorem fromBlocks_eq_of_invertible₁₁'
    (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α) [Invertible A] :
    Matrix.fromBlocks A B C D =
      Matrix.fromBlocks (1 : Matrix m m α) 0 (C * ⅟A) (1 : Matrix n n α) *
        Matrix.fromBlocks A 0 0 (complement₁₁ (A := A) (B := B) (C := C) (D := D)) *
          Matrix.fromBlocks (1 : Matrix m m α) (⅟A * B) 0 (1 : Matrix n n α) := by
  simpa [complement₁₁] using
    (Matrix.fromBlocks_eq_of_invertible₁₁ (A := A) (B := B) (C := C) (D := D))

end

end Schur

end Claim1lean


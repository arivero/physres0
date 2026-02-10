import Mathlib

namespace Claim1lean

/-! # Schur complement and determinant prefactors (finite-dimensional template)

This file packages mathlib's block-matrix determinant formulas in a form that we can cite
as the algebraic backbone of "integrate out intermediate variables ⇒ Schur complement +
determinant prefactor" (Van Vleck / Gaussian-elimination template).

No integration is formalized here; this is the purely algebraic determinant identity.
-/

namespace Schur

open Matrix

section

variable {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable [CommRing α]

def complement₁₁ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible A] : Matrix n n α :=
  D - C * ⅟A * B

def complement₂₂ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible D] : Matrix m m α :=
  A - B * ⅟D * C

theorem det_fromBlocks₁₁ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible A] :
    (Matrix.fromBlocks A B C D).det = det A * det (complement₁₁ (A := A) (B := B) (C := C) (D := D)) := by
  simpa [complement₁₁] using Matrix.det_fromBlocks₁₁ (A := A) (B := B) (C := C) (D := D)

theorem det_fromBlocks₂₂ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible D] :
    (Matrix.fromBlocks A B C D).det = det D * det (complement₂₂ (A := A) (B := B) (C := C) (D := D)) := by
  simpa [complement₂₂] using Matrix.det_fromBlocks₂₂ (A := A) (B := B) (C := C) (D := D)

theorem isUnit_fromBlocks_iff₁₁ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible A] :
    IsUnit (Matrix.fromBlocks A B C D) ↔ IsUnit (complement₁₁ (A := A) (B := B) (C := C) (D := D)) := by
  simpa [complement₁₁] using Matrix.isUnit_fromBlocks_iff_of_invertible₁₁ (A := A) (B := B) (C := C) (D := D)

theorem isUnit_fromBlocks_iff₂₂ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible D] :
    IsUnit (Matrix.fromBlocks A B C D) ↔ IsUnit (complement₂₂ (A := A) (B := B) (C := C) (D := D)) := by
  simpa [complement₂₂] using Matrix.isUnit_fromBlocks_iff_of_invertible₂₂ (A := A) (B := B) (C := C) (D := D)

end

end Schur

end Claim1lean


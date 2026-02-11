import Claim1lean.SchurComplementElimination

/-!
Van Vleck prefactor bridge (finite-dimensional algebraic lane).

This file turns Schur-complement determinant identities into prefactor product identities of the
form `det^{-1/2}` (implemented as `(|det|)^{-1/2}` over `ℝ`).

Interpretation: block elimination multiplies determinant-based normalization prefactors exactly in
the same way that Gaussian/Van-Vleck elimination formulas suggest.
-/

namespace Claim1lean

namespace VanVleck

open Matrix

/-- Determinant-based prefactor `(|det M|)^{-1/2}` used as a Van-Vleck-style algebraic proxy. -/
noncomputable def detPrefactor {k : Type*} [Fintype k] [DecidableEq k] (M : Matrix k k ℝ) : ℝ :=
  (Real.sqrt (|M.det|))⁻¹

lemma inv_sqrt_abs_mul (x y : ℝ) :
    (Real.sqrt (|x * y|))⁻¹ = (Real.sqrt |x|)⁻¹ * (Real.sqrt |y|)⁻¹ := by
  have hx : 0 ≤ |x| := abs_nonneg x
  calc
    (Real.sqrt (|x * y|))⁻¹ = (Real.sqrt (|x| * |y|))⁻¹ := by simp [abs_mul]
    _ = (Real.sqrt |x| * Real.sqrt |y|)⁻¹ := by rw [Real.sqrt_mul hx]
    _ = (Real.sqrt |y|)⁻¹ * (Real.sqrt |x|)⁻¹ := by
      simp [_root_.mul_inv_rev]
    _ = (Real.sqrt |x|)⁻¹ * (Real.sqrt |y|)⁻¹ := by
      simp [mul_comm]

section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem detPrefactor_fromBlocks₁₁
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ) (D : Matrix n n ℝ)
    [Invertible A] :
    detPrefactor (Matrix.fromBlocks A B C D) =
      detPrefactor A * detPrefactor (Schur.complement₁₁ (A := A) (B := B) (C := C) (D := D)) := by
  unfold detPrefactor
  rw [Schur.det_fromBlocks₁₁ (A := A) (B := B) (C := C) (D := D)]
  simpa using inv_sqrt_abs_mul (A.det) ((Schur.complement₁₁ (A := A) (B := B) (C := C) (D := D)).det)

theorem detPrefactor_fromBlocks₂₂
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ) (D : Matrix n n ℝ)
    [Invertible D] :
    detPrefactor (Matrix.fromBlocks A B C D) =
      detPrefactor D * detPrefactor (Schur.complement₂₂ (A := A) (B := B) (C := C) (D := D)) := by
  unfold detPrefactor
  rw [Schur.det_fromBlocks₂₂ (A := A) (B := B) (C := C) (D := D)]
  simpa using inv_sqrt_abs_mul (D.det) ((Schur.complement₂₂ (A := A) (B := B) (C := C) (D := D)).det)

end

end VanVleck

end Claim1lean

import Mathlib

namespace Claim1lean

/-! # Small-κ Lipschitz Prototype (Lean Core)

This file formalizes the analytic inequality pattern used in AN-5:
if a derivative is bounded on `[0, κ]`, then the increment is `O(κ)`.
-/

theorem lipschitz_from_derivWithin_bound
    {f : ℝ → ℝ} {C κ : ℝ}
    (hκ : 0 ≤ κ)
    (hf : DifferentiableOn ℝ f (Set.Icc (0 : ℝ) κ))
    (hbound : ∀ x ∈ Set.Ico (0 : ℝ) κ, ‖derivWithin f (Set.Icc (0 : ℝ) κ) x‖ ≤ C) :
    ‖f κ - f 0‖ ≤ C * κ := by
  have hk : κ ∈ Set.Icc (0 : ℝ) κ := ⟨hκ, le_rfl⟩
  simpa [sub_zero] using
    (norm_image_sub_le_of_norm_deriv_le_segment
      (a := (0 : ℝ)) (b := κ) (f := f) (C := C) hf hbound κ hk)

theorem lipschitz_unit_interval
    {f : ℝ → ℝ} {C : ℝ}
    (hf : DifferentiableOn ℝ f (Set.Icc (0 : ℝ) 1))
    (hbound : ∀ x ∈ Set.Ico (0 : ℝ) 1, ‖derivWithin f (Set.Icc (0 : ℝ) 1) x‖ ≤ C) :
    ‖f 1 - f 0‖ ≤ C := by
  simpa using norm_image_sub_le_of_norm_deriv_le_segment_01 (f := f) (C := C) hf hbound

end Claim1lean

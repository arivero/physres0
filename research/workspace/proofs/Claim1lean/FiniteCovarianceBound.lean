import Mathlib

namespace Claim1lean

/-! # Finite-Support Covariance-Type Bound (Lean)

Uniform-average finite model used as a bridge toward AN-5 covariance control.
-/

noncomputable section

def avg {n : Nat} (h : Fin (n + 1) → ℝ) : ℝ :=
  ((n + 1 : ℝ)⁻¹) * ∑ i, h i

theorem abs_avg_le_avg_abs {n : Nat} (h : Fin (n + 1) → ℝ) :
    |avg h| ≤ avg (fun i => |h i|) := by
  unfold avg
  have hfac : 0 ≤ ((n + 1 : ℝ)⁻¹) := by positivity
  calc
    |((n + 1 : ℝ)⁻¹ * ∑ i, h i)|
        = ((n + 1 : ℝ)⁻¹) * |∑ i, h i| := by
            simp [abs_mul, abs_of_nonneg hfac]
    _ ≤ ((n + 1 : ℝ)⁻¹) * ∑ i, |h i| := by
          gcongr
          exact Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := h)

theorem avg_centered_mul_le
    {n : Nat} (f g : Fin (n + 1) → ℝ) (c K : ℝ)
    (hK : ∀ i, |f i - c| ≤ K) :
    |avg (fun i => (f i - c) * g i)| ≤ K * avg (fun i => |g i|) := by
  have h0 :
      |avg (fun i => (f i - c) * g i)|
        ≤ avg (fun i => |(f i - c) * g i|) :=
    abs_avg_le_avg_abs (h := fun i => (f i - c) * g i)
  have h1 :
      avg (fun i => |(f i - c) * g i|)
        = avg (fun i => |f i - c| * |g i|) := by
    unfold avg
    simp [abs_mul]
  have hsum :
      (∑ i : Fin (n + 1), |f i - c| * |g i|)
        ≤ ∑ i : Fin (n + 1), K * |g i| := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact mul_le_mul_of_nonneg_right (hK i) (abs_nonneg (g i))
  have h2 :
      avg (fun i => |f i - c| * |g i|)
        ≤ avg (fun i => K * |g i|) := by
    unfold avg
    have hfac : 0 ≤ ((n + 1 : ℝ)⁻¹) := by positivity
    exact mul_le_mul_of_nonneg_left hsum hfac
  have h3 :
      avg (fun i => K * |g i|) = K * avg (fun i => |g i|) := by
    unfold avg
    calc
      ((n + 1 : ℝ)⁻¹ * ∑ i, K * |g i|)
          = ((n + 1 : ℝ)⁻¹) * (K * ∑ i, |g i|) := by
              simp [Finset.mul_sum]
      _ = K * (((n + 1 : ℝ)⁻¹) * ∑ i, |g i|) := by ring
      _ = K * avg (fun i => |g i|) := by rfl
  calc
    |avg (fun i => (f i - c) * g i)|
        ≤ avg (fun i => |(f i - c) * g i|) := h0
    _ = avg (fun i => |f i - c| * |g i|) := h1
    _ ≤ avg (fun i => K * |g i|) := h2
    _ = K * avg (fun i => |g i|) := h3

theorem avg_centered_mul_le_twoM
    {n : Nat} (f g : Fin (n + 1) → ℝ) (c M : ℝ)
    (hM : ∀ i, |f i - c| ≤ 2 * M) :
    |avg (fun i => (f i - c) * g i)| ≤ (2 * M) * avg (fun i => |g i|) := by
  exact avg_centered_mul_le f g c (2 * M) hM

end

end Claim1lean

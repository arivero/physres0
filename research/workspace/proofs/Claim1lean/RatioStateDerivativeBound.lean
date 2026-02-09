import Mathlib
import Claim1lean.CovarianceDerivative
import Claim1lean.FiniteCovarianceBound

namespace Claim1lean

/-! # Ratio-State Derivative Bound Template

AN-9 bridge: combine
1) quotient-derivative covariance form (AN-7),
2) finite centered-product inequality (AN-8),
into an abstract `|∂ω|` bound.
-/

theorem abs_deriv_ratio_le_of_centered_avg
    {N Z A B : ℝ → ℝ} {α x c K : ℝ}
    {n : Nat} (f g : Fin (n + 1) → ℝ)
    (hZ : Z x ≠ 0)
    (hN : HasDerivAt N (-α * A x) x)
    (hZ' : HasDerivAt Z (-α * B x) x)
    (hrepr :
      (A x) / (Z x) - (N x / Z x) * (B x / Z x)
        = avg (fun i => (f i - c) * g i))
    (hK : ∀ i, |f i - c| ≤ K) :
    |deriv (fun t => N t / Z t) x|
      ≤ |α| * (K * avg (fun i => |g i|)) := by
  have h7 := deriv_ratio_covariance_form (N := N) (Z := Z) (A := A) (B := B)
    (α := α) (x := x) hZ hN hZ'
  rw [h7]
  rw [hrepr]
  calc
    |(-α) * avg (fun i => (f i - c) * g i)|
        = |α| * |avg (fun i => (f i - c) * g i)| := by
            simp [abs_mul, abs_neg]
    _ ≤ |α| * (K * avg (fun i => |g i|)) := by
          gcongr
          exact avg_centered_mul_le (f := f) (g := g) (c := c) (K := K) hK

end Claim1lean

import Mathlib

namespace Claim1lean

/-! # Quotient-Derivative to Covariance Form (Lean)

This captures the algebraic core behind AN-5:
`ω = N/Z` with derivatives of numerator/denominator yields a covariance-type formula.
-/

theorem deriv_ratio_covariance_form
    {N Z A B : ℝ → ℝ} {α x : ℝ}
    (hZ : Z x ≠ 0)
    (hN : HasDerivAt N (-α * A x) x)
    (hZ' : HasDerivAt Z (-α * B x) x) :
    deriv (fun t => N t / Z t) x
      = (-α) * ((A x) / (Z x) - (N x / Z x) * (B x / Z x)) := by
  have hq : HasDerivAt (fun t => N t / Z t)
      (((-α * A x) * Z x - N x * (-α * B x)) / (Z x)^2) x :=
    hN.div hZ' hZ
  have hderiv :
      deriv (fun t => N t / Z t) x
        = (((-α * A x) * Z x - N x * (-α * B x)) / (Z x)^2) := by
    exact hq.deriv
  rw [hderiv]
  field_simp [hZ]
  ring

theorem deriv_ratio_covariance_form_alt
    {N Z A B : ℝ → ℝ} {α x : ℝ}
    (hZ : Z x ≠ 0)
    (hN : HasDerivAt N (-α * A x) x)
    (hZ' : HasDerivAt Z (-α * B x) x) :
    deriv (fun t => N t / Z t) x
      = (-α / Z x) * (A x - (N x / Z x) * B x) := by
  rw [deriv_ratio_covariance_form hZ hN hZ']
  field_simp [hZ]

end Claim1lean

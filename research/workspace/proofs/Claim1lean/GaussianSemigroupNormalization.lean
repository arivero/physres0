import Mathlib.Probability.Distributions.Gaussian.Real

/-!
Gaussian semigroup and normalization lane.

This is a Lean-side anchor for the "Gaussian/Van-Vleck prefactor" constraint behind
`t^{-d/2}`-type normalization in kernel composition: the *probability-measure* semigroup is
mathlib-native (`gaussianReal_conv_gaussianReal`), and the corresponding `gaussianPDFReal`
exhibits the `1 / sqrt(2*pi*v)` prefactor (hence `v^{-1/2}` scaling in 1D).

For now we keep this file 1D/real and measure-facing; higher-dimensional/product kernels can be
bootstrapped from these identities when needed.
-/

namespace Claim1lean

open scoped BigOperators NNReal Real

open MeasureTheory ProbabilityTheory

lemma gaussianReal_conv_zero {v₁ v₂ : ℝ≥0} :
    (ProbabilityTheory.gaussianReal (0 : ℝ) v₁) ∗ (ProbabilityTheory.gaussianReal (0 : ℝ) v₂) =
      ProbabilityTheory.gaussianReal (0 : ℝ) (v₁ + v₂) := by
  simpa using
    (ProbabilityTheory.gaussianReal_conv_gaussianReal (m₁ := (0 : ℝ)) (m₂ := (0 : ℝ))
      (v₁ := v₁) (v₂ := v₂))

lemma gaussianPDFReal_zero_at_zero (v : ℝ≥0) :
    ProbabilityTheory.gaussianPDFReal (0 : ℝ) v (0 : ℝ)
      = (√(2 * π * v))⁻¹ := by
  -- At `x = μ`, the exponential term is `exp 0 = 1`, leaving only the prefactor.
  simp [ProbabilityTheory.gaussianPDFReal]

lemma integral_gaussianPDFReal_eq_one_zero_mean {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ x, ProbabilityTheory.gaussianPDFReal (0 : ℝ) v x) = 1 := by
  simpa using (ProbabilityTheory.integral_gaussianPDFReal_eq_one (μ := (0 : ℝ)) (v := v) hv)

end Claim1lean

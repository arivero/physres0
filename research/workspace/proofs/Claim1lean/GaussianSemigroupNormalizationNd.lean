import Claim1lean.GaussianSemigroupNormalization

/-!
`d`-dimensional prefactor scaling for Gaussian semigroup normalization.

This file stays intentionally light: it upgrades the 1D diagonal prefactor witness
`gaussianPDFReal (μ=0,v)(0) = (2πv)^{-1/2}` to the product/exponent form that makes the
universal `v^{-d/2}` scaling transparent.

We do not formalize multivariate Gaussian measures/kernels here; the goal is to provide a
machine-checked algebraic bridge that can be cited in the Newton-limit paradox support lane.
-/

namespace Claim1lean

open scoped BigOperators NNReal Real

open MeasureTheory ProbabilityTheory

lemma gaussianPDFReal_zero_at_zero_pow (v : ℝ≥0) (d : ℕ) :
    (ProbabilityTheory.gaussianPDFReal (0 : ℝ) v (0 : ℝ)) ^ d
      = (Real.sqrt (2 * Real.pi))⁻¹ ^ d * (Real.sqrt (v : ℝ))⁻¹ ^ d := by
  -- Rewrite the 1D diagonal prefactor as a product, then raise to the `d`th power.
  simp [gaussianPDFReal_zero_at_zero_factor (v := v), mul_pow, mul_comm, mul_left_comm]

lemma gaussianPDFReal_zero_at_zero_pow' (v : ℝ≥0) (d : ℕ) :
    (ProbabilityTheory.gaussianPDFReal (0 : ℝ) v (0 : ℝ)) ^ d
      = (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ ^ d := by
  simp [gaussianPDFReal_zero_at_zero, mul_assoc]

end Claim1lean

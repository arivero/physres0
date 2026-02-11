import Claim1lean.GaussianSemigroupNormalizationNd

/-!
Gaussian scaling-rigidity lane (dimension-indexed).

This file turns the 1D Gaussian diagonal prefactor witness into a simple rigidity statement:
on `ℕ`, any multiplicative-in-addition family is fixed by its value at `1`.

Applied to Gaussian diagonal prefactors, this gives a machine-checked "forced exponent in `d`"
bridge: once the one-dimensional seed is fixed, the `d`-dimensional product normalization is
uniquely the `d`th power.
-/

namespace Claim1lean

open MeasureTheory ProbabilityTheory
open scoped NNReal Real

/-- One-dimensional diagonal Gaussian prefactor in mathlib normalization. -/
noncomputable def gaussianDiagPrefactor (v : ℝ≥0) : ℝ :=
  ProbabilityTheory.gaussianPDFReal (0 : ℝ) v (0 : ℝ)

/-- Product-model `d`-dimensional diagonal prefactor. -/
noncomputable def gaussianDimPrefactor (v : ℝ≥0) (d : ℕ) : ℝ :=
  (gaussianDiagPrefactor v) ^ d

lemma gaussianDimPrefactor_zero (v : ℝ≥0) :
    gaussianDimPrefactor v 0 = 1 := by
  simp [gaussianDimPrefactor]

lemma gaussianDimPrefactor_add (v : ℝ≥0) (d₁ d₂ : ℕ) :
    gaussianDimPrefactor v (d₁ + d₂) =
      gaussianDimPrefactor v d₁ * gaussianDimPrefactor v d₂ := by
  simp [gaussianDimPrefactor, pow_add]

/-- Additive-semigroup multiplicativity on `ℕ` is rigid once `f 0 = 1` is fixed. -/
lemma nat_multiplicative_rigidity {f : ℕ → ℝ}
    (hzero : f 0 = 1)
    (hadd : ∀ d₁ d₂ : ℕ, f (d₁ + d₂) = f d₁ * f d₂) :
    ∀ d : ℕ, f d = (f 1) ^ d := by
  intro d
  induction d with
  | zero =>
      simpa using hzero
  | succ d ih =>
      calc
        f (Nat.succ d) = f (d + 1) := by simp [Nat.succ_eq_add_one]
        _ = f d * f 1 := hadd d 1
        _ = (f 1) ^ d * f 1 := by simp [ih]
        _ = (f 1) ^ (Nat.succ d) := by simp [pow_succ]

/-- Rigidity: a dimension-indexed family with semigroup law and fixed `d=1` seed is unique. -/
theorem gaussianDimPrefactor_unique
    (v : ℝ≥0) (F : ℕ → ℝ)
    (hzero : F 0 = 1)
    (hadd : ∀ d₁ d₂ : ℕ, F (d₁ + d₂) = F d₁ * F d₂)
    (hone : F 1 = gaussianDiagPrefactor v) :
    ∀ d : ℕ, F d = gaussianDimPrefactor v d := by
  intro d
  calc
    F d = (F 1) ^ d := nat_multiplicative_rigidity (f := F) hzero hadd d
    _ = (gaussianDiagPrefactor v) ^ d := by simp [hone]
    _ = gaussianDimPrefactor v d := rfl

/-- Explicit `d`-power prefactor formula (`v^{-d/2}` structure in sqrt form). -/
theorem gaussianDimPrefactor_formula (v : ℝ≥0) (d : ℕ) :
    gaussianDimPrefactor v d
      = (Real.sqrt (2 * Real.pi))⁻¹ ^ d * (Real.sqrt (v : ℝ))⁻¹ ^ d := by
  simpa [gaussianDimPrefactor, gaussianDiagPrefactor] using
    gaussianPDFReal_zero_at_zero_pow (v := v) (d := d)

/-- Equivalent compact formula before factor splitting. -/
theorem gaussianDimPrefactor_formula' (v : ℝ≥0) (d : ℕ) :
    gaussianDimPrefactor v d = (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ ^ d := by
  simpa [gaussianDimPrefactor, gaussianDiagPrefactor] using
    gaussianPDFReal_zero_at_zero_pow' (v := v) (d := d)

/-- Counterexample lane: without fixing the `d=1` seed, multiplicative families are non-unique. -/
lemma nat_multiplicative_not_unique_without_seed :
    ∃ F G : ℕ → ℝ,
      (∀ d₁ d₂ : ℕ, F (d₁ + d₂) = F d₁ * F d₂) ∧
      (∀ d₁ d₂ : ℕ, G (d₁ + d₂) = G d₁ * G d₂) ∧
      F 1 ≠ G 1 := by
  refine ⟨(fun _ => (1 : ℝ)), (fun d => (2 : ℝ) ^ d), ?_, ?_, ?_⟩
  · intro d₁ d₂
    simp
  · intro d₁ d₂
    simp [pow_add]
  · norm_num

end Claim1lean

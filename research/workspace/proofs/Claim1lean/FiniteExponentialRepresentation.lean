import Mathlib
import Claim1lean.FiniteExponentialFamilyDeriv

namespace Claim1lean

/-! # Finite Exponential-Family Centered Representation Bridge

AN-15 bridge: recover the centered covariance representation directly from
finite-sum exponential-family data.
-/

noncomputable section

def omegaExp {n : Nat} (s f : Fin (n + 1) → ℝ) (κ : ℝ) : ℝ :=
  Nsum s f κ / Zsum s κ

def pExp {n : Nat} (s : Fin (n + 1) → ℝ) (κ : ℝ) (i : Fin (n + 1)) : ℝ :=
  Real.exp (-κ * s i) / Zsum s κ

theorem centered_weighted_sum_eq
    {n : Nat} (s f : Fin (n + 1) → ℝ) (κ : ℝ) :
    (∑ i, Real.exp (-κ * s i) * ((f i - omegaExp s f κ) * s i))
      = Asum s f κ - (omegaExp s f κ) * Bsum s κ := by
  have hpoint :
      ∀ i : Fin (n + 1),
        Real.exp (-κ * s i) * ((f i - omegaExp s f κ) * s i)
          = Real.exp (-κ * s i) * (f i * s i)
            - (omegaExp s f κ) * (Real.exp (-κ * s i) * s i) := by
    intro i
    ring
  calc
    ∑ i, Real.exp (-κ * s i) * ((f i - omegaExp s f κ) * s i)
        = ∑ i, (Real.exp (-κ * s i) * (f i * s i)
              - (omegaExp s f κ) * (Real.exp (-κ * s i) * s i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact hpoint i
    _ = (∑ i, Real.exp (-κ * s i) * (f i * s i))
        - (omegaExp s f κ) * (∑ i, Real.exp (-κ * s i) * s i) := by
            simp [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = Asum s f κ - (omegaExp s f κ) * Bsum s κ := by
            simp [Asum, Bsum, mul_comm, mul_assoc]

theorem covariance_repr_weighted_exp
    {n : Nat} (s f : Fin (n + 1) → ℝ) (κ : ℝ)
    (hZ : Zsum s κ ≠ 0) :
    (Asum s f κ) / (Zsum s κ) - (omegaExp s f κ) * ((Bsum s κ) / (Zsum s κ))
      = (∑ i, Real.exp (-κ * s i) * ((f i - omegaExp s f κ) * s i))
          / (Zsum s κ) := by
  have hcenter := centered_weighted_sum_eq (s := s) (f := f) (κ := κ)
  calc
    (Asum s f κ) / (Zsum s κ) - (omegaExp s f κ) * ((Bsum s κ) / (Zsum s κ))
        = (Asum s f κ - (omegaExp s f κ) * Bsum s κ) / (Zsum s κ) := by
            field_simp [hZ]
    _ = (∑ i, Real.exp (-κ * s i) * ((f i - omegaExp s f κ) * s i))
          / (Zsum s κ) := by
            rw [← hcenter]

theorem covariance_repr_weighted_prob
    {n : Nat} (s f : Fin (n + 1) → ℝ) (κ : ℝ)
    (hZ : Zsum s κ ≠ 0) :
    (Asum s f κ) / (Zsum s κ) - (omegaExp s f κ) * ((Bsum s κ) / (Zsum s κ))
      = ∑ i, pExp s κ i * ((f i - omegaExp s f κ) * s i) := by
  let t : Fin (n + 1) → ℝ := fun i => (f i - omegaExp s f κ) * s i
  calc
    (Asum s f κ) / (Zsum s κ) - (omegaExp s f κ) * ((Bsum s κ) / (Zsum s κ))
        = (∑ i, Real.exp (-κ * s i) * t i) / (Zsum s κ) := by
            simpa [t] using covariance_repr_weighted_exp (s := s) (f := f) (κ := κ) hZ
    _ = ∑ i, (Real.exp (-κ * s i) * t i) / (Zsum s κ) := by
          simp [Finset.sum_div]
    _ = ∑ i, (Real.exp (-κ * s i) / (Zsum s κ)) * t i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = ∑ i, pExp s κ i * ((f i - omegaExp s f κ) * s i) := by
          simp [pExp, t]

end

end Claim1lean

import Mathlib
import Claim1lean.RatioStateIncrementBound
import Claim1lean.FiniteExponentialDerivativeBound
import Claim1lean.FiniteExponentialRegularity

namespace Claim1lean

/-! # Finite Exponential-Family Interval Increment Bridge

AN-17 bridge: lift BE derivative control to AN-10 style `Cκ` interval bounds
under explicit uniform-on-interval assumptions.
-/

noncomputable section

theorem omegaExp_increment_bound_of_uniform_centered_control
    {n : Nat} (s f : Fin (n + 1) → ℝ) {κ K M : ℝ}
    (hκ : 0 ≤ κ)
    (hDiff : DifferentiableOn ℝ (fun t => Nsum s f t / Zsum s t) (Set.Icc (0 : ℝ) κ))
    (hwithin : ∀ t ∈ Set.Ico (0 : ℝ) κ,
      derivWithin (fun t => Nsum s f t / Zsum s t) (Set.Icc (0 : ℝ) κ) t
        = deriv (fun t => Nsum s f t / Zsum s t) t)
    (hKnonneg : 0 ≤ K)
    (hZ : ∀ t ∈ Set.Ico (0 : ℝ) κ, Zsum s t ≠ 0)
    (hcenter : ∀ t ∈ Set.Ico (0 : ℝ) κ, ∀ i, |f i - omegaExp s f t| ≤ K)
    (hMoment : ∀ t ∈ Set.Ico (0 : ℝ) κ, ∑ i, |pExp s t i| * |s i| ≤ M) :
    |(Nsum s f κ / Zsum s κ) - (Nsum s f 0 / Zsum s 0)| ≤ (K * M) * κ := by
  apply ratio_increment_bound_from_pointwise_deriv
      (N := Nsum s f) (Z := Zsum s) (C := K * M) (κ := κ)
      hκ hDiff hwithin
  intro t ht
  have hderiv :=
    abs_deriv_omegaExp_le_centered_bound
      (s := s) (f := f) (κ := t) (K := K) (hZ t ht) (hcenter t ht)
  calc
    |deriv (fun t => Nsum s f t / Zsum s t) t|
        ≤ K * ∑ i, |pExp s t i| * |s i| := hderiv
    _ ≤ K * M := by
          exact mul_le_mul_of_nonneg_left (hMoment t ht) hKnonneg

theorem omegaExp_increment_bound_of_uniform_centered_control_auto
    {n : Nat} (s f : Fin (n + 1) → ℝ) {κ K M : ℝ}
    (hκ : 0 ≤ κ)
    (hKnonneg : 0 ≤ K)
    (hcenter : ∀ t ∈ Set.Ico (0 : ℝ) κ, ∀ i, |f i - omegaExp s f t| ≤ K)
    (hMoment : ∀ t ∈ Set.Ico (0 : ℝ) κ, ∑ i, |pExp s t i| * |s i| ≤ M) :
    |(Nsum s f κ / Zsum s κ) - (Nsum s f 0 / Zsum s 0)| ≤ (K * M) * κ := by
  by_cases hκ0 : κ = 0
  · subst hκ0
    simp
  · have hκpos : 0 < κ := lt_of_le_of_ne hκ (Ne.symm hκ0)
    refine omegaExp_increment_bound_of_uniform_centered_control
      (s := s) (f := f) (κ := κ) (K := K) (M := M)
      hκ (differentiableOn_omegaExp_Icc (s := s) (f := f) (κ := κ)) ?_ hKnonneg ?_ hcenter hMoment
    · intro t ht
      exact derivWithin_omegaExp_Icc_eq_deriv
        (s := s) (f := f) (hκ := hκpos) (ht := ⟨ht.1, le_of_lt ht.2⟩)
    · intro t ht
      exact Zsum_ne_zero (s := s) (κ := t)

theorem omegaExp_increment_bound_of_uniform_centered_control_auto_renormalizedScale
    {n : Nat} (a : ℝ) (s f : Fin (n + 1) → ℝ) {κ K Mren : ℝ}
    (hκ : 0 ≤ κ)
    (hKnonneg : 0 ≤ K)
    (hcenter : ∀ t ∈ Set.Ico (0 : ℝ) κ, ∀ i,
      |f i - omegaExp (fun j => (a ^ (3 : Nat)) * s j) f t| ≤ K)
    (hMomentRen : ∀ t ∈ Set.Ico (0 : ℝ) κ,
      ∑ i, |pExp (fun j => (a ^ (3 : Nat)) * s j) t i| * |(a ^ (3 : Nat)) * s i| ≤ Mren) :
    |(Nsum (fun j => (a ^ (3 : Nat)) * s j) f κ
      / Zsum (fun j => (a ^ (3 : Nat)) * s j) κ)
      - (Nsum (fun j => (a ^ (3 : Nat)) * s j) f 0
        / Zsum (fun j => (a ^ (3 : Nat)) * s j) 0)|
      ≤ (K * Mren) * κ := by
  exact omegaExp_increment_bound_of_uniform_centered_control_auto
    (s := fun j => (a ^ (3 : Nat)) * s j) (f := f)
    (κ := κ) (K := K) (M := Mren) hκ hKnonneg hcenter hMomentRen

end

end Claim1lean

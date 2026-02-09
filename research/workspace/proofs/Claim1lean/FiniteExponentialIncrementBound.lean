import Mathlib
import Claim1lean.RatioStateIncrementBound
import Claim1lean.FiniteExponentialDerivativeBound

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

end

end Claim1lean

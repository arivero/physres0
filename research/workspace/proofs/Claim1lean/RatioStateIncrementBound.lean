import Mathlib
import Claim1lean.SmallKappaLipschitz
import Claim1lean.RatioStateDerivativeBound

namespace Claim1lean

/-! # Ratio-State Increment Bound on an Interval

AN-10 bridge: turn pointwise derivative control into interval increment control.
-/

theorem ratio_increment_bound_from_derivWithin
    {N Z : ℝ → ℝ} {C κ : ℝ}
    (hκ : 0 ≤ κ)
    (hDiff : DifferentiableOn ℝ (fun t => N t / Z t) (Set.Icc (0 : ℝ) κ))
    (hbound : ∀ t ∈ Set.Ico (0 : ℝ) κ,
      ‖derivWithin (fun t => N t / Z t) (Set.Icc (0 : ℝ) κ) t‖ ≤ C) :
    |(N κ / Z κ) - (N 0 / Z 0)| ≤ C * κ := by
  have h :=
    lipschitz_from_derivWithin_bound
      (f := fun t => N t / Z t) (C := C) (κ := κ) hκ hDiff hbound
  simpa [Real.norm_eq_abs, sub_eq_add_neg] using h

theorem derivWithin_Icc_eq_deriv_of_mem_Ioo
    {f : ℝ → ℝ} {κ t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) κ) :
    derivWithin f (Set.Icc (0 : ℝ) κ) t = deriv f t := by
  exact derivWithin_of_mem_nhds (s := Set.Icc (0 : ℝ) κ) (x := t) (Icc_mem_nhds ht.1 ht.2)

theorem ratio_increment_bound_from_pointwise_deriv
    {N Z : ℝ → ℝ} {C κ : ℝ}
    (hκ : 0 ≤ κ)
    (hDiff : DifferentiableOn ℝ (fun t => N t / Z t) (Set.Icc (0 : ℝ) κ))
    (hwithin : ∀ t ∈ Set.Ico (0 : ℝ) κ,
      derivWithin (fun t => N t / Z t) (Set.Icc (0 : ℝ) κ) t
        = deriv (fun t => N t / Z t) t)
    (hpoint : ∀ t ∈ Set.Ico (0 : ℝ) κ,
      |deriv (fun t => N t / Z t) t| ≤ C) :
    |(N κ / Z κ) - (N 0 / Z 0)| ≤ C * κ := by
  apply ratio_increment_bound_from_derivWithin (N := N) (Z := Z) (C := C) (κ := κ) hκ hDiff
  intro t ht
  rw [hwithin t ht, Real.norm_eq_abs]
  exact hpoint t ht

theorem ratio_increment_bound_from_pointwise_deriv_with_boundary
    {N Z : ℝ → ℝ} {C κ : ℝ}
    (hκ : 0 ≤ κ)
    (hDiff : DifferentiableOn ℝ (fun t => N t / Z t) (Set.Icc (0 : ℝ) κ))
    (hbound0 : ‖derivWithin (fun t => N t / Z t) (Set.Icc (0 : ℝ) κ) 0‖ ≤ C)
    (hpoint : ∀ t ∈ Set.Ioo (0 : ℝ) κ,
      |deriv (fun t => N t / Z t) t| ≤ C) :
    |(N κ / Z κ) - (N 0 / Z 0)| ≤ C * κ := by
  apply ratio_increment_bound_from_derivWithin (N := N) (Z := Z) (C := C) (κ := κ) hκ hDiff
  intro t ht
  by_cases h0 : t = 0
  · simpa [h0] using hbound0
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h0)
    have hIoo : t ∈ Set.Ioo (0 : ℝ) κ := ⟨htpos, ht.2⟩
    rw [derivWithin_Icc_eq_deriv_of_mem_Ioo hIoo, Real.norm_eq_abs]
    exact hpoint t hIoo

theorem ratio_increment_bound_from_centered_avg_template
    {N Z A B : ℝ → ℝ} {α κ c K : ℝ}
    {n : Nat} (f g : Fin (n + 1) → ℝ)
    (hκ : 0 ≤ κ)
    (hDiff : DifferentiableOn ℝ (fun t => N t / Z t) (Set.Icc (0 : ℝ) κ))
    (hwithin : ∀ t ∈ Set.Ico (0 : ℝ) κ,
      derivWithin (fun t => N t / Z t) (Set.Icc (0 : ℝ) κ) t
        = deriv (fun t => N t / Z t) t)
    (hZ : ∀ t ∈ Set.Ico (0 : ℝ) κ, Z t ≠ 0)
    (hN : ∀ t ∈ Set.Ico (0 : ℝ) κ, HasDerivAt N (-α * A t) t)
    (hZ' : ∀ t ∈ Set.Ico (0 : ℝ) κ, HasDerivAt Z (-α * B t) t)
    (hrepr : ∀ t ∈ Set.Ico (0 : ℝ) κ,
      (A t) / (Z t) - (N t / Z t) * (B t / Z t)
        = avg (fun i => (f i - c) * g i))
    (hK : ∀ i, |f i - c| ≤ K) :
    |(N κ / Z κ) - (N 0 / Z 0)|
      ≤ (|α| * (K * avg (fun i => |g i|))) * κ := by
  apply ratio_increment_bound_from_pointwise_deriv
      (N := N) (Z := Z) (C := |α| * (K * avg (fun i => |g i|))) (κ := κ)
      hκ hDiff hwithin
  intro t ht
  exact abs_deriv_ratio_le_of_centered_avg
      (f := f) (g := g) (N := N) (Z := Z) (A := A) (B := B)
      (α := α) (x := t) (c := c) (K := K)
      (hZ t ht) (hN t ht) (hZ' t ht) (hrepr t ht) hK

theorem ratio_increment_bound_from_centered_avg_template_with_boundary
    {N Z A B : ℝ → ℝ} {α κ c K : ℝ}
    {n : Nat} (f g : Fin (n + 1) → ℝ)
    (hκ : 0 ≤ κ)
    (hDiff : DifferentiableOn ℝ (fun t => N t / Z t) (Set.Icc (0 : ℝ) κ))
    (hbound0 : ‖derivWithin (fun t => N t / Z t) (Set.Icc (0 : ℝ) κ) 0‖
      ≤ (|α| * (K * avg (fun i => |g i|))))
    (hZ : ∀ t ∈ Set.Ioo (0 : ℝ) κ, Z t ≠ 0)
    (hN : ∀ t ∈ Set.Ioo (0 : ℝ) κ, HasDerivAt N (-α * A t) t)
    (hZ' : ∀ t ∈ Set.Ioo (0 : ℝ) κ, HasDerivAt Z (-α * B t) t)
    (hrepr : ∀ t ∈ Set.Ioo (0 : ℝ) κ,
      (A t) / (Z t) - (N t / Z t) * (B t / Z t)
        = avg (fun i => (f i - c) * g i))
    (hK : ∀ i, |f i - c| ≤ K) :
    |(N κ / Z κ) - (N 0 / Z 0)|
      ≤ (|α| * (K * avg (fun i => |g i|))) * κ := by
  apply ratio_increment_bound_from_pointwise_deriv_with_boundary
      (N := N) (Z := Z) (C := |α| * (K * avg (fun i => |g i|))) (κ := κ)
      hκ hDiff hbound0
  intro t ht
  exact abs_deriv_ratio_le_of_centered_avg
      (f := f) (g := g) (N := N) (Z := Z) (A := A) (B := B)
      (α := α) (x := t) (c := c) (K := K)
      (hZ t ht) (hN t ht) (hZ' t ht) (hrepr t ht) hK

theorem derivWithin_Icc_zero_eq_derivWithin_Ici_zero
    {f : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ) :
    derivWithin f (Set.Icc (0 : ℝ) κ) 0
      = derivWithin f (Set.Ici (0 : ℝ)) 0 := by
  have hset : Set.Icc (0 : ℝ) κ = Set.Ici (0 : ℝ) ∩ Set.Iic κ := by
    ext t
    simp [Set.mem_Icc, Set.mem_Ici, Set.mem_Iic]
  calc
    derivWithin f (Set.Icc (0 : ℝ) κ) 0
        = derivWithin f (Set.Ici (0 : ℝ) ∩ Set.Iic κ) 0 := by simp [hset]
    _ = derivWithin f (Set.Ici (0 : ℝ)) 0 := by
          simpa using
            (derivWithin_inter (f := f) (s := Set.Ici (0 : ℝ)) (t := Set.Iic κ) (x := (0 : ℝ))
              (Iic_mem_nhds hκ))

theorem ratio_increment_bound_from_centered_avg_template_oneSidedBoundary
    {N Z A B : ℝ → ℝ} {α κ c K : ℝ}
    {n : Nat} (f g : Fin (n + 1) → ℝ)
    (hκ : 0 < κ)
    (hDiff : DifferentiableOn ℝ (fun t => N t / Z t) (Set.Icc (0 : ℝ) κ))
    (hbound0 : ‖derivWithin (fun t => N t / Z t) (Set.Ici (0 : ℝ)) 0‖
      ≤ (|α| * (K * avg (fun i => |g i|))))
    (hZ : ∀ t ∈ Set.Ioo (0 : ℝ) κ, Z t ≠ 0)
    (hN : ∀ t ∈ Set.Ioo (0 : ℝ) κ, HasDerivAt N (-α * A t) t)
    (hZ' : ∀ t ∈ Set.Ioo (0 : ℝ) κ, HasDerivAt Z (-α * B t) t)
    (hrepr : ∀ t ∈ Set.Ioo (0 : ℝ) κ,
      (A t) / (Z t) - (N t / Z t) * (B t / Z t)
        = avg (fun i => (f i - c) * g i))
    (hK : ∀ i, |f i - c| ≤ K) :
    |(N κ / Z κ) - (N 0 / Z 0)|
      ≤ (|α| * (K * avg (fun i => |g i|))) * κ := by
  have hκ0 : 0 ≤ κ := le_of_lt hκ
  have hbound0Icc : ‖derivWithin (fun t => N t / Z t) (Set.Icc (0 : ℝ) κ) 0‖
      ≤ (|α| * (K * avg (fun i => |g i|))) := by
    rw [derivWithin_Icc_zero_eq_derivWithin_Ici_zero (f := fun t => N t / Z t) hκ]
    exact hbound0
  exact ratio_increment_bound_from_centered_avg_template_with_boundary
      (f := f) (g := g) (hκ := hκ0) hDiff hbound0Icc hZ hN hZ' hrepr hK

end Claim1lean

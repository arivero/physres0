import Mathlib
import Claim1lean.FiniteExponentialRepresentation

namespace Claim1lean

/-! # Finite Exponential-Family Automatic Regularity

AN-18 bridge: discharge regularity side-assumptions for the finite exponential
family used in AN-17.
-/

noncomputable section

theorem Zsum_pos {n : Nat} (s : Fin (n + 1) → ℝ) (κ : ℝ) :
    0 < Zsum s κ := by
  unfold Zsum
  refine Finset.sum_pos' ?_ ?_
  · intro i hi
    exact (Real.exp_pos _).le
  · refine ⟨⟨0, Nat.succ_pos n⟩, by simp, ?_⟩
    exact Real.exp_pos _

theorem Zsum_ne_zero {n : Nat} (s : Fin (n + 1) → ℝ) (κ : ℝ) :
    Zsum s κ ≠ 0 :=
  (Zsum_pos (s := s) (κ := κ)).ne'

theorem differentiable_Nsum {n : Nat} (s f : Fin (n + 1) → ℝ) :
    Differentiable ℝ (Nsum s f) := by
  intro κ
  exact (hasDerivAt_Nsum (s := s) (f := f) (κ := κ)).differentiableAt

theorem differentiable_Zsum {n : Nat} (s : Fin (n + 1) → ℝ) :
    Differentiable ℝ (Zsum s) := by
  intro κ
  exact (hasDerivAt_Zsum (s := s) (κ := κ)).differentiableAt

theorem differentiable_omegaExp {n : Nat} (s f : Fin (n + 1) → ℝ) :
    Differentiable ℝ (fun t => Nsum s f t / Zsum s t) := by
  intro κ
  exact ((hasDerivAt_Nsum (s := s) (f := f) (κ := κ)).div
      (hasDerivAt_Zsum (s := s) (κ := κ))
      (Zsum_ne_zero (s := s) (κ := κ))).differentiableAt

theorem differentiableOn_omegaExp_Icc {n : Nat} (s f : Fin (n + 1) → ℝ) (κ : ℝ) :
    DifferentiableOn ℝ (fun t => Nsum s f t / Zsum s t) (Set.Icc (0 : ℝ) κ) := by
  intro t ht
  exact (differentiable_omegaExp (s := s) (f := f) t).differentiableWithinAt

end

end Claim1lean

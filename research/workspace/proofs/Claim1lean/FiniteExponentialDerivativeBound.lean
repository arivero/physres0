import Mathlib
import Claim1lean.CovarianceDerivative
import Claim1lean.FiniteExponentialFamilyDeriv
import Claim1lean.FiniteExponentialRepresentation

namespace Claim1lean

/-! # Finite Exponential-Family Derivative Bound Bridge

AN-16 bridge: derive model-internal `|∂ω|` bounds from AN-14 + AN-15.
-/

noncomputable section

theorem abs_deriv_omegaExp_le_weighted_abs
    {n : Nat} (s f : Fin (n + 1) → ℝ) (κ : ℝ)
    (hZ : Zsum s κ ≠ 0) :
    |deriv (fun t => Nsum s f t / Zsum s t) κ|
      ≤ ∑ i, |pExp s κ i| * (|f i - omegaExp s f κ| * |s i|) := by
  have hderiv :=
    deriv_ratio_covariance_form
      (N := Nsum s f) (Z := Zsum s) (A := Asum s f) (B := Bsum s)
      (α := (1 : ℝ)) (x := κ)
      hZ
      (by simpa [one_mul] using hasDerivAt_Nsum (s := s) (f := f) (κ := κ))
      (by simpa [one_mul] using hasDerivAt_Zsum (s := s) (κ := κ))
  rw [hderiv]
  have hrepr := covariance_repr_weighted_prob (s := s) (f := f) (κ := κ) hZ
  have hrepr' :
      Asum s f κ / Zsum s κ - Nsum s f κ / Zsum s κ * (Bsum s κ / Zsum s κ)
        = ∑ i, pExp s κ i * ((f i - omegaExp s f κ) * s i) := by
    simpa [omegaExp] using hrepr
  rw [hrepr']
  calc
    |(- (1 : ℝ)) * ∑ i, pExp s κ i * ((f i - omegaExp s f κ) * s i)|
        = |∑ i, pExp s κ i * ((f i - omegaExp s f κ) * s i)| := by
            simp
    _ ≤ ∑ i, |pExp s κ i * ((f i - omegaExp s f κ) * s i)| := by
          exact Finset.abs_sum_le_sum_abs (s := Finset.univ)
            (f := fun i : Fin (n + 1) => pExp s κ i * ((f i - omegaExp s f κ) * s i))
    _ = ∑ i, |pExp s κ i| * (|f i - omegaExp s f κ| * |s i|) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [abs_mul, mul_left_comm, mul_comm]

theorem abs_deriv_omegaExp_le_centered_bound
    {n : Nat} (s f : Fin (n + 1) → ℝ) (κ K : ℝ)
    (hZ : Zsum s κ ≠ 0)
    (hK : ∀ i, |f i - omegaExp s f κ| ≤ K) :
    |deriv (fun t => Nsum s f t / Zsum s t) κ|
      ≤ K * ∑ i, |pExp s κ i| * |s i| := by
  have hbase := abs_deriv_omegaExp_le_weighted_abs (s := s) (f := f) (κ := κ) hZ
  calc
    |deriv (fun t => Nsum s f t / Zsum s t) κ|
        ≤ ∑ i, |pExp s κ i| * (|f i - omegaExp s f κ| * |s i|) := hbase
    _ ≤ ∑ i, |pExp s κ i| * (K * |s i|) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hfi : |f i - omegaExp s f κ| * |s i| ≤ K * |s i| :=
            mul_le_mul_of_nonneg_right (hK i) (abs_nonneg (s i))
          exact mul_le_mul_of_nonneg_left hfi (abs_nonneg (pExp s κ i))
    _ = K * ∑ i, |pExp s κ i| * |s i| := by
          calc
            ∑ i, |pExp s κ i| * (K * |s i|)
                = ∑ i, K * (|pExp s κ i| * |s i|) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    ring
            _ = K * ∑ i, |pExp s κ i| * |s i| := by
                    simp [Finset.mul_sum]

end

end Claim1lean

import Mathlib

namespace Claim1lean

/-! # Finite Exponential-Family Derivative Bridge

Finite-sum surrogate for parameter-differentiation under integral.
This supplies concrete `HasDerivAt` hypotheses feeding AN-7 templates.
-/

noncomputable section

def Nsum {n : Nat} (s f : Fin (n + 1) → ℝ) (κ : ℝ) : ℝ :=
  ∑ i, Real.exp (-κ * s i) * f i

def Zsum {n : Nat} (s : Fin (n + 1) → ℝ) (κ : ℝ) : ℝ :=
  ∑ i, Real.exp (-κ * s i)

def Asum {n : Nat} (s f : Fin (n + 1) → ℝ) (κ : ℝ) : ℝ :=
  ∑ i, Real.exp (-κ * s i) * (s i * f i)

def Bsum {n : Nat} (s : Fin (n + 1) → ℝ) (κ : ℝ) : ℝ :=
  ∑ i, Real.exp (-κ * s i) * s i

theorem hasDerivAt_exp_neg_mul_const (a κ : ℝ) :
    HasDerivAt (fun t => Real.exp (-t * a)) (-(a * Real.exp (-κ * a))) κ := by
  have hlin : HasDerivAt (fun t => (-(a : ℝ)) * t) (-(a : ℝ)) κ := by
    simpa using (hasDerivAt_id κ).const_mul (-(a : ℝ))
  have hcomp : HasDerivAt (fun t => Real.exp ((-(a : ℝ)) * t))
      (Real.exp ((-(a : ℝ)) * κ) * (-(a : ℝ))) κ :=
    (Real.hasDerivAt_exp ((-(a : ℝ)) * κ)).comp κ hlin
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcomp

theorem hasDerivAt_Nsum {n : Nat} (s f : Fin (n + 1) → ℝ) (κ : ℝ) :
    HasDerivAt (Nsum s f) (-(Asum s f κ)) κ := by
  unfold Nsum Asum
  have hterm :
      ∀ i : Fin (n + 1),
        HasDerivAt
          (fun t => Real.exp (-t * s i) * f i)
          (-(Real.exp (-κ * s i) * (s i * f i))) κ := by
    intro i
    have hExp := hasDerivAt_exp_neg_mul_const (a := s i) (κ := κ)
    have hMul : HasDerivAt
        (fun t => Real.exp (-t * s i) * f i)
        (-(s i * Real.exp (-κ * s i)) * f i) κ := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hExp.mul_const (f i)
    simpa [mul_comm, mul_left_comm, mul_assoc, neg_mul, mul_neg] using hMul
  have hsum :=
    HasDerivAt.fun_sum (u := Finset.univ)
      (A := fun i => fun t => Real.exp (-t * s i) * f i)
      (A' := fun i => -(Real.exp (-κ * s i) * (s i * f i)))
      (x := κ)
      (h := fun i hi => hterm i)
  change HasDerivAt (fun t => ∑ i ∈ Finset.univ, Real.exp (-t * s i) * f i) (-(Asum s f κ)) κ
  simpa [Asum, Finset.sum_neg_distrib] using hsum

theorem hasDerivAt_Zsum {n : Nat} (s : Fin (n + 1) → ℝ) (κ : ℝ) :
    HasDerivAt (Zsum s) (-(Bsum s κ)) κ := by
  unfold Zsum Bsum
  have hterm :
      ∀ i : Fin (n + 1),
        HasDerivAt
          (fun t => Real.exp (-t * s i))
          (-(Real.exp (-κ * s i) * s i)) κ := by
    intro i
    simpa [mul_comm, mul_left_comm, mul_assoc, neg_mul, mul_neg] using
      hasDerivAt_exp_neg_mul_const (a := s i) (κ := κ)
  have hsum :=
    HasDerivAt.fun_sum (u := Finset.univ)
      (A := fun i => fun t => Real.exp (-t * s i))
      (A' := fun i => -(Real.exp (-κ * s i) * s i))
      (x := κ)
      (h := fun i hi => hterm i)
  change HasDerivAt (fun t => ∑ i ∈ Finset.univ, Real.exp (-t * s i)) (-(Bsum s κ)) κ
  simpa [Bsum, Finset.sum_neg_distrib] using hsum

end

end Claim1lean

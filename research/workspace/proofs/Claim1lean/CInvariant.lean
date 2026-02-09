import Mathlib

namespace Claim1lean

/-! # Claim 1 `c`-Invariance Core (Lean)

This module formalizes the algebraic core used repeatedly in the notes:
`tau`-reparameterization preserves

`c = (η - i / h) κ`.
-/

noncomputable section

structure Params where
  κ : ℂ
  η : ℂ
  h : ℂ

/-- Kernel parameter in the Claim 1 chain. -/
def cParam (p : Params) : ℂ :=
  (p.η - Complex.I / p.h) * p.κ

/-- `τ_μ` reparameterization. -/
def tau (μ : ℂ) (p : Params) : Params :=
  { κ := μ * p.κ
    η := p.η / μ
    h := μ * p.h }

@[simp] theorem tau_kappa (μ : ℂ) (p : Params) : (tau μ p).κ = μ * p.κ := rfl
@[simp] theorem tau_eta (μ : ℂ) (p : Params) : (tau μ p).η = p.η / μ := rfl
@[simp] theorem tau_h (μ : ℂ) (p : Params) : (tau μ p).h = μ * p.h := rfl

/-- Exact `c`-invariance along `tau μ` orbits (`μ ≠ 0`). -/
theorem cParam_tau (μ : ℂ) (p : Params) (hμ : μ ≠ 0) :
    cParam (tau μ p) = cParam p := by
  rcases p with ⟨κ, η, h⟩
  unfold cParam tau
  field_simp [hμ]

/-- `tau` composes multiplicatively in the scale parameter. -/
theorem tau_compose (μ₁ μ₂ : ℂ) (p : Params) :
    tau μ₁ (tau μ₂ p) = tau (μ₁ * μ₂) p := by
  rcases p with ⟨κ, η, h⟩
  simp [tau, div_eq_mul_inv, mul_left_comm, mul_comm]

@[simp] theorem tau_one (p : Params) : tau 1 p = p := by
  rcases p with ⟨κ, η, h⟩
  simp [tau]

/-- For nonzero `μ`, `tau (1/μ)` is a left inverse to `tau μ`. -/
theorem tau_leftInverse (μ : ℂ) (p : Params) (hμ : μ ≠ 0) :
    tau (1 / μ) (tau μ p) = p := by
  rcases p with ⟨κ, η, h⟩
  simp [tau, hμ, div_eq_mul_inv, mul_comm]

/-- Observables depending only on `cParam` are invariant along nonzero `tau μ` orbits. -/
def IsCInvariant {α : Type} (O : Params → α) : Prop :=
  ∀ p q, cParam p = cParam q → O p = O q

theorem invariant_along_tau {α : Type} (O : Params → α)
    (hO : IsCInvariant O) (μ : ℂ) (p : Params) (hμ : μ ≠ 0) :
    O (tau μ p) = O p :=
  hO (tau μ p) p (cParam_tau μ p hμ)

end

end Claim1lean

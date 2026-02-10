import Mathlib

namespace Claim1lean

/-! # Semigroup → generator (right-derivative ODE)

A minimal semigroup→generator fact used in the "Newton-limit paradox" support lane.

If `R` is a (right-action) semigroup of maps on a normed space `E`,
`R (s+t) = R t ∘ R s`, and each trajectory `t ↦ R t x` has a right derivative at `0`
with value `β x`, then the orbit `g(t) = R t x0` satisfies the right-derivative
ODE `g'(t+) = β (g t)`.
-/

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable (R : ℝ → E → E) (β : E → E)

/-- Orbit `g(t) = R t x0` has right derivative `β(g t)` at any `t ≥ 0`. -/
theorem orbit_hasDerivWithinAt_Ici
    (hsemigroup : ∀ {s t : ℝ} {x : E}, 0 ≤ s → 0 ≤ t → R (s + t) x = R t (R s x))
    (hzero : ∀ x : E, R 0 x = x)
    (hderiv0 : ∀ x : E, HasDerivWithinAt (fun t : ℝ => R t x) (β x) (Set.Ici (0 : ℝ)) 0)
    {x0 : E} {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun u : ℝ => R u x0) (β (R t x0)) (Set.Ici t) t := by
  -- Rewrite the orbit on `[t, ∞)` using the semigroup property.
  have horbit : ∀ u ∈ Set.Ici t, R u x0 = R (u - t) (R t x0) := by
    intro u hu
    have hst : 0 ≤ u - t := by
      exact sub_nonneg.mpr (by simpa using hu)
    have hsum : t + (u - t) = u := by ring
    calc
      R u x0 = R (t + (u - t)) x0 := by simp [hsum]
      _ = R (u - t) (R t x0) := (hsemigroup (s := t) (t := (u - t)) (x := x0) ht hst)

  -- Differentiate the right-hand side `u ↦ R (u-t) (R t x0)` at `u=t` within `[t, ∞)`.
  have htrans : HasDerivWithinAt (fun u : ℝ => u - t) (1 : ℝ) (Set.Ici t) t := by
    simpa using ((hasDerivAt_id t).sub_const t).hasDerivWithinAt

  have hmap : Set.MapsTo (fun u : ℝ => u - t) (Set.Ici t) (Set.Ici (0 : ℝ)) := by
    intro u hu
    exact sub_nonneg.mpr (by simpa using hu)

  have htraj : HasDerivWithinAt (fun s : ℝ => R s (R t x0)) (β (R t x0)) (Set.Ici (0 : ℝ)) 0 :=
    hderiv0 (R t x0)

  have hcomp : HasDerivWithinAt (fun u : ℝ => R (u - t) (R t x0)) (β (R t x0)) (Set.Ici t) t := by
    simpa [Function.comp, one_smul] using
      (HasDerivWithinAt.scomp_of_eq (x := t) (hg := htraj) (hh := htrans) (hst := hmap)
        (by simp))

  -- Transfer derivative to the orbit using equality on the within-set.
  have hx : R t x0 = R (t - t) (R t x0) := by
    simp [sub_self, hzero]

  exact hcomp.congr horbit hx

end

end Claim1lean


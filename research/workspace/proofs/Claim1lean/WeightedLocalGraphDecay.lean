import Mathlib

namespace Claim1lean

/-! # Weighted-Local and Graph-Decay Finite Surrogate Bounds

AN-32L support lane: machine-checked finite bounds for weighted-local truncation,
graph-decay nonlocal channels, and denominator-rate ratio bookkeeping.
-/

noncomputable section

def weightedL1 {n : Nat} (w x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i, |w i| * |x i|

def weightedTailL1 {n : Nat} (w χ x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i, (1 - χ i) * |w i| * |x i|

theorem weightedTailL1_le_of_uniform_bound
    {n : Nat} (w χ x : Fin (n + 1) → ℝ) {M : ℝ}
    (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ 1)
    (hx : ∀ i, |x i| ≤ M) :
    weightedTailL1 w χ x ≤ M * ∑ i, (1 - χ i) * |w i| := by
  unfold weightedTailL1
  calc
    ∑ i, (1 - χ i) * |w i| * |x i|
        ≤ ∑ i, (1 - χ i) * |w i| * M := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hchi_le : χ i ≤ 1 := (hχ i).2
          have hfac_nonneg : 0 ≤ (1 - χ i) * |w i| := by
            exact mul_nonneg (sub_nonneg.mpr hchi_le) (abs_nonneg (w i))
          exact mul_le_mul_of_nonneg_left (hx i) hfac_nonneg
    _ = M * ∑ i, (1 - χ i) * |w i| := by
          calc
            ∑ i, (1 - χ i) * |w i| * M
                = ∑ i, M * ((1 - χ i) * |w i|) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    ring
            _ = M * ∑ i, (1 - χ i) * |w i| := by
                    simp [Finset.mul_sum]

theorem weightedL1_image_le_of_column_decay
    {m n : Nat} (v : Fin (m + 1) → ℝ) (w : Fin (n + 1) → ℝ)
    (K : Fin (m + 1) → Fin (n + 1) → ℝ) (x : Fin (n + 1) → ℝ) {C : ℝ}
    (hcol : ∀ j, ∑ i, |v i| * |K i j| ≤ C * |w j|) :
    ∑ i, |v i| * |∑ j, K i j * x j| ≤ C * weightedL1 w x := by
  calc
    ∑ i, |v i| * |∑ j, K i j * x j|
        ≤ ∑ i, ∑ j, |v i| * (|K i j| * |x j|) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have habs :
              |∑ j, K i j * x j| ≤ ∑ j, |K i j * x j| := by
            exact Finset.abs_sum_le_sum_abs (s := Finset.univ)
              (f := fun j : Fin (n + 1) => K i j * x j)
          have hmul :
              |v i| * |∑ j, K i j * x j|
                ≤ |v i| * ∑ j, |K i j * x j| :=
            mul_le_mul_of_nonneg_left habs (abs_nonneg (v i))
          calc
            |v i| * |∑ j, K i j * x j|
                ≤ |v i| * ∑ j, |K i j * x j| := hmul
            _ = ∑ j, |v i| * (|K i j| * |x j|) := by
                  calc
                    |v i| * ∑ j, |K i j * x j|
                        = ∑ j, |v i| * |K i j * x j| := by
                            simp [Finset.mul_sum]
                    _ = ∑ j, |v i| * (|K i j| * |x j|) := by
                          refine Finset.sum_congr rfl ?_
                          intro j hj
                          simp [abs_mul]
    _ = ∑ j, ∑ i, |v i| * (|K i j| * |x j|) := by
          simpa using (Finset.sum_comm :
            (∑ i : Fin (m + 1), ∑ j : Fin (n + 1), |v i| * (|K i j| * |x j|))
              = ∑ j : Fin (n + 1), ∑ i : Fin (m + 1), |v i| * (|K i j| * |x j|))
    _ = ∑ j, (∑ i, |v i| * |K i j|) * |x j| := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          calc
            ∑ i, |v i| * (|K i j| * |x j|)
                = ∑ i, (|v i| * |K i j|) * |x j| := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    ring
            _ = (∑ i, |v i| * |K i j|) * |x j| := by
                    simp [Finset.sum_mul]
    _ ≤ ∑ j, (C * |w j|) * |x j| := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact mul_le_mul_of_nonneg_right (hcol j) (abs_nonneg (x j))
    _ = C * weightedL1 w x := by
          unfold weightedL1
          calc
            ∑ j, (C * |w j|) * |x j|
                = ∑ j, C * (|w j| * |x j|) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    ring
            _ = C * ∑ j, |w j| * |x j| := by
                    simp [Finset.mul_sum]

theorem abs_inv_sub_inv_le_of_abs_sub_le
    {D D' εD d0 : ℝ}
    (hd0 : 0 < d0)
    (hD : d0 ≤ |D|)
    (hD' : d0 ≤ |D'|)
    (hDerr : |D - D'| ≤ εD) :
    |1 / D - 1 / D'| ≤ εD / (d0 * d0) := by
  have hεDnonneg : 0 ≤ εD := by
    nlinarith [abs_nonneg (D - D'), hDerr]
  have hDabs_pos : 0 < |D| := lt_of_lt_of_le hd0 hD
  have hD'abs_pos : 0 < |D'| := lt_of_lt_of_le hd0 hD'
  have hDnz : D ≠ 0 := by
    exact abs_pos.mp hDabs_pos
  have hD'nz : D' ≠ 0 := by
    exact abs_pos.mp hD'abs_pos
  have hrepr : 1 / D - 1 / D' = (D' - D) / (D * D') := by
    field_simp [hDnz, hD'nz]
  have hprod_lower : d0 * d0 ≤ |D| * |D'| := by
    nlinarith [hD, hD', le_of_lt hd0, abs_nonneg D, abs_nonneg D']
  have hprod_pos : 0 < |D| * |D'| := mul_pos hDabs_pos hD'abs_pos
  have hnum :
      |D' - D| ≤ εD := by
    simpa [abs_sub_comm] using hDerr
  calc
    |1 / D - 1 / D'|
        = |(D' - D) / (D * D')| := by rw [hrepr]
    _ = |D' - D| / (|D| * |D'|) := by
          simp [abs_div, abs_mul]
    _ ≤ εD / (|D| * |D'|) := by
          exact div_le_div_of_nonneg_right hnum (le_of_lt hprod_pos)
    _ ≤ εD / (d0 * d0) := by
          exact div_le_div_of_nonneg_left hεDnonneg (mul_pos hd0 hd0) hprod_lower

theorem ratio_diff_bound_of_num_and_reciprocal_rate
    {N N' D D' εN εInv d0 B : ℝ}
    (hd0 : 0 < d0)
    (hD : d0 ≤ |D|)
    (hN : |N - N'| ≤ εN)
    (hInv : |1 / D - 1 / D'| ≤ εInv)
    (hB : |N'| ≤ B) :
    |N / D - N' / D'| ≤ εN / d0 + B * εInv := by
  have hεInv_nonneg : 0 ≤ εInv := by
    nlinarith [abs_nonneg (1 / D - 1 / D'), hInv]
  have hterm1 :
      |(N - N') / D| ≤ εN / d0 := by
    calc
      |(N - N') / D|
          = |N - N'| / |D| := by simp [abs_div]
      _ ≤ |N - N'| / d0 := by
            exact div_le_div_of_nonneg_left (abs_nonneg (N - N')) hd0 hD
      _ ≤ εN / d0 := by
            exact div_le_div_of_nonneg_right hN (le_of_lt hd0)
  have hterm2 :
      |N' * (1 / D - 1 / D')| ≤ B * εInv := by
    calc
      |N' * (1 / D - 1 / D')|
          = |N'| * |1 / D - 1 / D'| := by simp [abs_mul]
      _ ≤ |N'| * εInv := by
            exact mul_le_mul_of_nonneg_left hInv (abs_nonneg N')
      _ ≤ B * εInv := by
            exact mul_le_mul_of_nonneg_right hB hεInv_nonneg
  have hsplit :
      N / D - N' / D' = (N - N') / D + N' * (1 / D - 1 / D') := by
    ring
  have hsum :
      |(N - N') / D + N' * (1 / D - 1 / D')|
        ≤ |N - N'| / |D| + |N' * (1 / D - 1 / D')| := by
    simpa [Real.norm_eq_abs, abs_div] using
      (norm_add_le ((N - N') / D) (N' * (1 / D - 1 / D')))
  calc
    |N / D - N' / D'|
        = |(N - N') / D + N' * (1 / D - 1 / D')| := by rw [hsplit]
    _ ≤ |(N - N') / D| + |N' * (1 / D - 1 / D')| := by
          simpa [abs_div] using hsum
    _ ≤ εN / d0 + B * εInv := add_le_add hterm1 hterm2

theorem ratio_diff_bound_of_denominator_rates
    {N N' D D' εN εD d0 B : ℝ}
    (hd0 : 0 < d0)
    (hD : d0 ≤ |D|)
    (hD' : d0 ≤ |D'|)
    (hN : |N - N'| ≤ εN)
    (hDerr : |D - D'| ≤ εD)
    (hB : |N'| ≤ B) :
    |N / D - N' / D'| ≤ εN / d0 + B * (εD / (d0 * d0)) := by
  have hInv :=
    abs_inv_sub_inv_le_of_abs_sub_le
      (D := D) (D' := D') (εD := εD) (d0 := d0) hd0 hD hD' hDerr
  exact ratio_diff_bound_of_num_and_reciprocal_rate
    (N := N) (N' := N') (D := D) (D' := D')
    (εN := εN) (εInv := εD / (d0 * d0)) (d0 := d0) (B := B)
    hd0 hD hN hInv hB

end

end Claim1lean

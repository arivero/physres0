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

theorem ratio_diff_bound_of_tail_rates
    {N N' D D' t AN AD d0 B : ℝ}
    (hd0 : 0 < d0)
    (hD : d0 ≤ |D|)
    (hD' : d0 ≤ |D'|)
    (hN : |N - N'| ≤ AN * t)
    (hDerr : |D - D'| ≤ AD * t)
    (hB : |N'| ≤ B) :
    |N / D - N' / D'|
      ≤ (AN / d0 + B * (AD / (d0 * d0))) * t := by
  have hbase :=
    ratio_diff_bound_of_denominator_rates
      (N := N) (N' := N') (D := D) (D' := D')
      (εN := AN * t) (εD := AD * t) (d0 := d0) (B := B)
      hd0 hD hD' hN hDerr hB
  calc
    |N / D - N' / D'|
        ≤ (AN * t) / d0 + B * ((AD * t) / (d0 * d0)) := hbase
    _ = (AN / d0 + B * (AD / (d0 * d0))) * t := by ring

theorem abs_sub_le_add_of_dist_to_center
    {x y c ex ey : ℝ}
    (hx : |x - c| ≤ ex)
    (hy : |y - c| ≤ ey) :
    |x - y| ≤ ex + ey := by
  have hsplit : x - y = (x - c) + (c - y) := by ring
  calc
    |x - y|
        = |(x - c) + (c - y)| := by rw [hsplit]
    _ ≤ |x - c| + |c - y| := by
          simpa [Real.norm_eq_abs] using norm_add_le (x - c) (c - y)
    _ = |x - c| + |y - c| := by
          simp [abs_sub_comm]
    _ ≤ ex + ey := add_le_add hx hy

theorem abs_sub_le_of_tail_to_limit
    {x y c A tx ty : ℝ}
    (hx : |x - c| ≤ A * tx)
    (hy : |y - c| ≤ A * ty) :
    |x - y| ≤ A * (tx + ty) := by
  have hbase :=
    abs_sub_le_add_of_dist_to_center
      (x := x) (y := y) (c := c)
      (ex := A * tx) (ey := A * ty) hx hy
  calc
    |x - y|
        ≤ A * tx + A * ty := hbase
    _ = A * (tx + ty) := by ring

theorem ratio_diff_bound_of_limit_tail_rates
    {Nn Nm Dn Dm Nlim Dlim tn tm AN AD d0 B : ℝ}
    (hd0 : 0 < d0)
    (hDn : d0 ≤ |Dn|)
    (hDm : d0 ≤ |Dm|)
    (hNn : |Nn - Nlim| ≤ AN * tn)
    (hNm : |Nm - Nlim| ≤ AN * tm)
    (hDnTail : |Dn - Dlim| ≤ AD * tn)
    (hDmTail : |Dm - Dlim| ≤ AD * tm)
    (hB : |Nm| ≤ B) :
    |Nn / Dn - Nm / Dm|
      ≤ (AN / d0 + B * (AD / (d0 * d0))) * (tn + tm) := by
  have hNpair :
      |Nn - Nm| ≤ AN * (tn + tm) :=
    abs_sub_le_of_tail_to_limit
      (x := Nn) (y := Nm) (c := Nlim) (A := AN) (tx := tn) (ty := tm) hNn hNm
  have hDpair :
      |Dn - Dm| ≤ AD * (tn + tm) :=
    abs_sub_le_of_tail_to_limit
      (x := Dn) (y := Dm) (c := Dlim) (A := AD) (tx := tn) (ty := tm) hDnTail hDmTail
  exact ratio_diff_bound_of_tail_rates
    (N := Nn) (N' := Nm) (D := Dn) (D' := Dm)
    (t := tn + tm) (AN := AN) (AD := AD) (d0 := d0) (B := B)
    hd0 hDn hDm hNpair hDpair hB

theorem pairwise_tail_rate_of_exhaustion_envelope
    {u t : Nat → ℝ} {ulim A : ℝ}
    (huTail : ∀ n, |u n - ulim| ≤ A * t n) :
    ∀ n m, |u n - u m| ≤ A * (t n + t m) := by
  intro n m
  exact abs_sub_le_of_tail_to_limit
    (x := u n) (y := u m) (c := ulim)
    (A := A) (tx := t n) (ty := t m)
    (huTail n) (huTail m)

theorem pairwise_add_rate_of_exhaustion_envelopes
    {u v t : Nat → ℝ} {ulim vlim Au Av : ℝ}
    (huTail : ∀ n, |u n - ulim| ≤ Au * t n)
    (hvTail : ∀ n, |v n - vlim| ≤ Av * t n) :
    ∀ n m, |(u n + v n) - (u m + v m)| ≤ (Au + Av) * (t n + t m) := by
  intro n m
  have huPair :
      |u n - u m| ≤ Au * (t n + t m) :=
    pairwise_tail_rate_of_exhaustion_envelope
      (u := u) (t := t) (ulim := ulim) (A := Au) huTail n m
  have hvPair :
      |v n - v m| ≤ Av * (t n + t m) :=
    pairwise_tail_rate_of_exhaustion_envelope
      (u := v) (t := t) (ulim := vlim) (A := Av) hvTail n m
  have hsplit :
      (u n + v n) - (u m + v m) = (u n - u m) + (v n - v m) := by
    ring
  calc
    |(u n + v n) - (u m + v m)|
        = |(u n - u m) + (v n - v m)| := by rw [hsplit]
    _ ≤ |u n - u m| + |v n - v m| := by
          simpa [Real.norm_eq_abs] using norm_add_le (u n - u m) (v n - v m)
    _ ≤ Au * (t n + t m) + Av * (t n + t m) := add_le_add huPair hvPair
    _ = (Au + Av) * (t n + t m) := by ring

theorem pairwise_ratio_rate_of_exhaustion_envelopes
    {N D t : Nat → ℝ} {Nlim Dlim AN AD d0 B : ℝ}
    (hd0 : 0 < d0)
    (hDfloor : ∀ n, d0 ≤ |D n|)
    (hNtail : ∀ n, |N n - Nlim| ≤ AN * t n)
    (hDtail : ∀ n, |D n - Dlim| ≤ AD * t n)
    (hNbound : ∀ n, |N n| ≤ B) :
    ∀ n m, |N n / D n - N m / D m|
      ≤ (AN / d0 + B * (AD / (d0 * d0))) * (t n + t m) := by
  intro n m
  exact ratio_diff_bound_of_limit_tail_rates
    (Nn := N n) (Nm := N m) (Dn := D n) (Dm := D m)
    (Nlim := Nlim) (Dlim := Dlim)
    (tn := t n) (tm := t m)
    (AN := AN) (AD := AD) (d0 := d0) (B := B)
    hd0 (hDfloor n) (hDfloor m)
    (hNtail n) (hNtail m) (hDtail n) (hDtail m) (hNbound m)

theorem abs_le_add_of_abs_sub_le
    {x y ex ey : ℝ}
    (hxy : |x - y| ≤ ex)
    (hy : |y| ≤ ey) :
    |x| ≤ ex + ey := by
  have hsplit : x = (x - y) + y := by linarith
  have habs : |x| = |(x - y) + y| := congrArg abs hsplit
  calc
    |x| = |(x - y) + y| := habs
    _ ≤ |x - y| + |y| := by
          simpa [Real.norm_eq_abs] using norm_add_le (x - y) y
    _ ≤ ex + ey := add_le_add hxy hy

theorem projective_defect_transfer_of_regularization
    {δ0 δη t : Nat → ℝ} {A B e : ℝ}
    (hClose : ∀ n, |δ0 n - δη n| ≤ B * e)
    (hEtaDefect : ∀ n, |δη n| ≤ A * t n) :
    ∀ n, |δ0 n| ≤ A * t n + B * e := by
  intro n
  have hbase :=
    abs_le_add_of_abs_sub_le
      (x := δ0 n) (y := δη n)
      (ex := B * e) (ey := A * t n)
      (hClose n) (hEtaDefect n)
  calc
    |δ0 n| ≤ B * e + A * t n := hbase
    _ = A * t n + B * e := by ring

theorem pairwise_transfer_bound_of_regularization
    {u0 uη t : Nat → ℝ} {A B e : ℝ}
    (hReg : ∀ n, |u0 n - uη n| ≤ B * e)
    (hPairη : ∀ n m, |uη n - uη m| ≤ A * (t n + t m)) :
    ∀ n m, |u0 n - u0 m| ≤ A * (t n + t m) + 2 * (B * e) := by
  intro n m
  have hsplit :
      u0 n - u0 m
        = (u0 n - uη n) + (uη n - uη m) + (uη m - u0 m) := by
    ring
  calc
    |u0 n - u0 m|
        = |(u0 n - uη n) + (uη n - uη m) + (uη m - u0 m)| := by rw [hsplit]
    _ ≤ |(u0 n - uη n) + (uη n - uη m)| + |uη m - u0 m| := by
          simpa [Real.norm_eq_abs] using
            norm_add_le ((u0 n - uη n) + (uη n - uη m)) (uη m - u0 m)
    _ ≤ (|u0 n - uη n| + |uη n - uη m|) + |uη m - u0 m| := by
          refine add_le_add ?_ (le_rfl)
          simpa [Real.norm_eq_abs] using norm_add_le (u0 n - uη n) (uη n - uη m)
    _ ≤ (B * e + A * (t n + t m)) + B * e := by
          refine add_le_add ?_ ?_
          · exact add_le_add (hReg n) (hPairη n m)
          · simpa [abs_sub_comm] using hReg m
    _ = A * (t n + t m) + 2 * (B * e) := by ring

theorem pairwise_transfer_bound_between_regularizations
    {uη uη' uref t : Nat → ℝ} {A B eη eη' : ℝ}
    (hη : ∀ n, |uη n - uref n| ≤ B * eη)
    (hη' : ∀ n, |uη' n - uref n| ≤ B * eη')
    (hPairRef : ∀ n m, |uref n - uref m| ≤ A * (t n + t m)) :
    ∀ n m, |uη n - uη' m| ≤ A * (t n + t m) + B * eη + B * eη' := by
  intro n m
  have hsplit :
      uη n - uη' m
        = (uη n - uref n) + (uref n - uref m) + (uref m - uη' m) := by
    ring
  calc
    |uη n - uη' m|
        = |(uη n - uref n) + (uref n - uref m) + (uref m - uη' m)| := by
            rw [hsplit]
    _ ≤ |(uη n - uref n) + (uref n - uref m)| + |uref m - uη' m| := by
          simpa [Real.norm_eq_abs] using
            norm_add_le ((uη n - uref n) + (uref n - uref m)) (uref m - uη' m)
    _ ≤ (|uη n - uref n| + |uref n - uref m|) + |uref m - uη' m| := by
          refine add_le_add ?_ (le_rfl)
          simpa [Real.norm_eq_abs] using norm_add_le (uη n - uref n) (uref n - uref m)
    _ ≤ (B * eη + A * (t n + t m)) + B * eη' := by
          refine add_le_add ?_ ?_
          · exact add_le_add (hη n) (hPairRef n m)
          · simpa [abs_sub_comm] using hη' m
    _ = A * (t n + t m) + B * eη + B * eη' := by ring

end

end Claim1lean

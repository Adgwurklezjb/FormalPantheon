import Arithmetic.LcmIntervalGaps

/-!
The exact harmonic main term in CDT v2 Section 2.2, supplied TeX
3330-3341. Natural quotient endpoints and all prime-power gap weights
are retained before applying the uniform PNT interval estimate.
-/

namespace DirichletL

/-- The harmonic exponent for the positive interval lcm, with value zero at width zero. -/
noncomputable def lcmIntervalMainTerm (n k : ℕ) : ℝ :=
  (k : ℝ) * (harmonic (n / k - 1) : ℝ) + (n : ℝ) / ((n / k : ℕ) : ℝ)

theorem lcmIntervalMainTerm_nonneg (n k : ℕ) : 0 ≤ lcmIntervalMainTerm n k := by
  have hh : (0 : ℚ) ≤ harmonic (n / k - 1) := by
    unfold harmonic
    exact Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  exact add_nonneg (mul_nonneg (Nat.cast_nonneg k) (Rat.cast_nonneg.mpr hh))
    (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg _))

theorem sum_interval_gap_lengths (n k : ℝ) (M : ℕ) :
    (∑ a ∈ Finset.Icc 1 M, ((n - k) / (a : ℝ) - n / ((a : ℝ) + 1))) =
      n - k * (harmonic M : ℝ) - n / ((M : ℝ) + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, harmonic_succ]
    push_cast
    ring

theorem lcmIntervalGap_length_nonneg {n k a : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (ha : a ∈ Finset.Icc 1 (n / k - 1)) :
    0 ≤ ((n - k : ℕ) : ℝ) / (a : ℝ) - (n : ℝ) / ((a : ℝ) + 1) := by
  have ha' := Finset.mem_Icc.mp ha
  have haR : (0 : ℝ) < a := by exact_mod_cast ha'.1
  have hM : 0 < n / k := Nat.div_pos hkn hk
  have ham : a + 1 ≤ n / k := by omega
  have hmul : (a + 1) * k ≤ n := (Nat.le_div_iff_mul_le hk).mp ham
  have hmulR : ((a : ℝ) + 1) * (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmul
  rw [Nat.cast_sub hkn, sub_nonneg, div_le_div_iff₀ (by positivity) haR]
  nlinarith

theorem sum_lcmIntervalGap_lengths (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    (∑ a ∈ Finset.Icc 1 (n / k - 1),
      max (((n - k : ℕ) : ℝ) / (a : ℝ) - (n : ℝ) / ((a : ℝ) + 1)) 0) =
        (n : ℝ) - lcmIntervalMainTerm n k := by
  have hsum : (∑ a ∈ Finset.Icc 1 (n / k - 1),
      max (((n - k : ℕ) : ℝ) / (a : ℝ) - (n : ℝ) / ((a : ℝ) + 1)) 0) =
      ∑ a ∈ Finset.Icc 1 (n / k - 1),
        (((n : ℝ) - (k : ℝ)) / (a : ℝ) - (n : ℝ) / ((a : ℝ) + 1)) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [max_eq_left (lcmIntervalGap_length_nonneg hk hkn ha), Nat.cast_sub hkn]
  have hM : 1 ≤ n / k := Nat.div_pos hkn hk
  have hcast : (((n / k - 1 : ℕ) : ℝ) + 1) = ((n / k : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hM
  rw [hsum, sum_interval_gap_lengths, hcast, lcmIntervalMainTerm]
  ring

end DirichletL

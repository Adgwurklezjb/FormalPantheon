import Arithmetic.LcmIntervalQuotientMainTerm

/-!
Exact clipped gap lengths for CDT v2 Section 2.2, supplied TeX 3383-3411.
The zero-index case is separated before using the last gap endpoint.
-/

namespace DirichletL

/-- The length of one missing-prime-power interval above the cutoff. -/
noncomputable def lcmIntervalQuotientGapLength (n k c a : ℕ) : ℝ :=
  max (((n - k : ℕ) : ℝ) / (a : ℝ) - max (c : ℝ) ((n : ℝ) / ((a : ℝ) + 1))) 0

theorem lcmIntervalQuotientGapLength_eq_zero {n k c a : ℕ}
    (hk : 0 < k) (hkn : k ≤ n) (ha : lcmIntervalQuotientIndex n k c < a) :
    lcmIntervalQuotientGapLength n k c a = 0 := by
  have ha0 : 0 < a := (Nat.zero_le _).trans_lt ha
  have haR : (0 : ℝ) < a := by exact_mod_cast ha0
  have hD : 0 < max k c := hk.trans_le (le_max_left _ _)
  have hmul : n - k < a * max k c := (Nat.div_lt_iff_lt_mul hD).mp ha
  have hupper : ((n - k : ℕ) : ℝ) / (a : ℝ) ≤
      max (c : ℝ) ((n : ℝ) / ((a : ℝ) + 1)) := by
    by_cases hck : c ≤ k
    · rw [max_eq_left hck] at hmul
      have hmulR : (n : ℝ) - (k : ℝ) < (a : ℝ) * (k : ℝ) := by
        exact_mod_cast hmul
      apply le_trans _ (le_max_right _ _)
      rw [Nat.cast_sub hkn, div_le_div_iff₀ haR (by positivity)]
      nlinarith
    · rw [max_eq_right (le_of_not_ge hck)] at hmul
      have hmulR : ((n - k : ℕ) : ℝ) < (a : ℝ) * (c : ℝ) := by
        exact_mod_cast hmul
      apply le_trans _ (le_max_left _ _)
      apply (div_le_iff₀ haR).mpr
      nlinarith
  exact max_eq_right (sub_nonpos.mpr hupper)

theorem lcmIntervalQuotientGapLength_eq_uncut {n k c a : ℕ}
    (hk : 0 < k) (hkn : k ≤ n) (ha : 1 ≤ a)
    (haM : a < lcmIntervalQuotientIndex n k c) :
    lcmIntervalQuotientGapLength n k c a =
      ((n - k : ℕ) : ℝ) / (a : ℝ) - (n : ℝ) / ((a : ℝ) + 1) := by
  have hMc : lcmIntervalQuotientIndex n k c * c ≤ n - k :=
    (Nat.mul_le_mul_left _ (le_max_right k c)).trans (Nat.div_mul_le_self _ _)
  have hac : (a + 1) * c ≤ n :=
    ((Nat.mul_le_mul_right c (Nat.succ_le_iff.mpr haM)).trans hMc).trans (Nat.sub_le n k)
  have hclip : (c : ℝ) ≤ (n : ℝ) / ((a : ℝ) + 1) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have h : ((a : ℝ) + 1) * (c : ℝ) ≤ (n : ℝ) := by exact_mod_cast hac
    nlinarith
  have hlength := lcmIntervalGap_length_nonneg hk hkn
    (Finset.mem_Icc.mpr ⟨ha, haM.le.trans (lcmIntervalQuotientIndex_le hk hkn)⟩)
  rw [lcmIntervalQuotientGapLength, max_eq_right hclip, max_eq_left hlength]

theorem lcmIntervalQuotientGapLength_last {n k c : ℕ}
    (hk : 0 < k) (hkn : k ≤ n) (hM : 0 < lcmIntervalQuotientIndex n k c) :
    lcmIntervalQuotientGapLength n k c (lcmIntervalQuotientIndex n k c) =
      ((n - k : ℕ) : ℝ) / (lcmIntervalQuotientIndex n k c : ℝ) -
        (n : ℝ) / ((lcmIntervalQuotientIndex n k c : ℝ) + 1) -
          max ((c : ℝ) - (n : ℝ) / ((lcmIntervalQuotientIndex n k c : ℝ) + 1)) 0 := by
  have hMR : (0 : ℝ) < lcmIntervalQuotientIndex n k c := by exact_mod_cast hM
  have hMc : lcmIntervalQuotientIndex n k c * c ≤ n - k :=
    (Nat.mul_le_mul_left _ (le_max_right k c)).trans (Nat.div_mul_le_self _ _)
  have hupper : (c : ℝ) ≤ ((n - k : ℕ) : ℝ) / (lcmIntervalQuotientIndex n k c : ℝ) := by
    apply (le_div_iff₀ hMR).mpr
    have h : (lcmIntervalQuotientIndex n k c : ℝ) * (c : ℝ) ≤ ((n - k : ℕ) : ℝ) := by
      exact_mod_cast hMc
    nlinarith
  have hlength := lcmIntervalGap_length_nonneg hk hkn
    (Finset.mem_Icc.mpr ⟨hM, lcmIntervalQuotientIndex_le hk hkn⟩)
  unfold lcmIntervalQuotientGapLength
  by_cases hclip : (c : ℝ) ≤ (n : ℝ) / ((lcmIntervalQuotientIndex n k c : ℝ) + 1)
  · rw [max_eq_right hclip, max_eq_left hlength,
      max_eq_right (sub_nonpos.mpr hclip), sub_zero]
  · rw [max_eq_left (le_of_not_ge hclip), max_eq_left (sub_nonneg.mpr hupper),
      max_eq_left (sub_nonneg.mpr (le_of_not_ge hclip))]
    ring

theorem sum_lcmIntervalQuotientGap_lengths {n k c : ℕ}
    (hk : 0 < k) (hkn : k ≤ n) (hcn : c ≤ n) :
    (∑ a ∈ Finset.Icc 1 (n / k - 1), lcmIntervalQuotientGapLength n k c a) =
      (n : ℝ) - (c : ℝ) - lcmIntervalQuotientMainTerm n k c := by
  let M := lcmIntervalQuotientIndex n k c
  let U (a : ℕ) : ℝ := ((n : ℝ) - (k : ℝ)) / (a : ℝ) - (n : ℝ) / ((a : ℝ) + 1)
  have hsubset : Finset.Icc 1 M ⊆ Finset.Icc 1 (n / k - 1) := by
    intro a ha
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1,
      (Finset.mem_Icc.mp ha).2.trans (lcmIntervalQuotientIndex_le hk hkn)⟩
  have hsum : (∑ a ∈ Finset.Icc 1 (n / k - 1), lcmIntervalQuotientGapLength n k c a) =
      ∑ a ∈ Finset.Icc 1 M, lcmIntervalQuotientGapLength n k c a := by
    symm
    apply Finset.sum_subset hsubset
    intro a ha hnot
    have ha1 := (Finset.mem_Icc.mp ha).1
    have haM : M < a := by
      by_contra! h
      exact hnot (Finset.mem_Icc.mpr ⟨ha1, h⟩)
    exact lcmIntervalQuotientGapLength_eq_zero hk hkn haM
  rw [hsum, lcmIntervalQuotientMainTerm, if_neg hk.ne']
  change (∑ a ∈ Finset.Icc 1 M, lcmIntervalQuotientGapLength n k c a) =
    (n : ℝ) - (c : ℝ) - ((k : ℝ) * (harmonic M : ℝ) +
      max ((n : ℝ) / ((M : ℝ) + 1) - (c : ℝ)) 0)
  by_cases hM : M = 0
  · rw [hM]
    simp only [Finset.Icc_eq_empty_of_lt (by omega : 0 < (1 : ℕ)), Finset.sum_empty,
      harmonic_zero, Rat.cast_zero, Nat.cast_zero, zero_add, div_one, mul_zero]
    rw [max_eq_left (sub_nonneg.mpr (by exact_mod_cast hcn))]
    ring
  · have hM0 : 0 < M := Nat.pos_of_ne_zero hM
    have hsumU : (∑ a ∈ Finset.Icc 1 (M - 1), lcmIntervalQuotientGapLength n k c a) =
        ∑ a ∈ Finset.Icc 1 (M - 1), U a := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha' := Finset.mem_Icc.mp ha
      rw [lcmIntervalQuotientGapLength_eq_uncut hk hkn ha'.1 (by omega), Nat.cast_sub hkn]
    have hsplit : (∑ a ∈ Finset.Icc 1 M, lcmIntervalQuotientGapLength n k c a) =
        (∑ a ∈ Finset.Icc 1 (M - 1), U a) + lcmIntervalQuotientGapLength n k c M := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ M - 1 + 1 by omega)
        (lcmIntervalQuotientGapLength n k c)
      rw [Nat.sub_add_cancel hM0, hsumU] at h
      exact h
    have hsplitU : (∑ a ∈ Finset.Icc 1 M, U a) = (∑ a ∈ Finset.Icc 1 (M - 1), U a) + U M := by
      simpa only [Nat.sub_add_cancel hM0] using
        Finset.sum_Icc_succ_top (show 1 ≤ M - 1 + 1 by omega) U
    have hlast := lcmIntervalQuotientGapLength_last hk hkn hM0
    change lcmIntervalQuotientGapLength n k c M = _ at hlast
    rw [Nat.cast_sub hkn] at hlast
    change lcmIntervalQuotientGapLength n k c M =
      U M - max ((c : ℝ) - (n : ℝ) / ((M : ℝ) + 1)) 0 at hlast
    have ht : (∑ a ∈ Finset.Icc 1 M, U a) =
        (n : ℝ) - (k : ℝ) * (harmonic M : ℝ) - (n : ℝ) / ((M : ℝ) + 1) :=
      sum_interval_gap_lengths (n : ℝ) (k : ℝ) M
    calc
      _ = (∑ a ∈ Finset.Icc 1 M, U a) - max ((c : ℝ) - (n : ℝ) / ((M : ℝ) + 1)) 0 := by
        rw [hsplit, hlast, hsplitU]
        ring
      _ = _ := by
        rw [ht]
        by_cases hclip : (c : ℝ) ≤ (n : ℝ) / ((M : ℝ) + 1)
        · rw [max_eq_right (sub_nonpos.mpr hclip), max_eq_left (sub_nonneg.mpr hclip)]
          ring
        · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hclip)),
            max_eq_right (sub_nonpos.mpr (le_of_not_ge hclip))]
          ring

end DirichletL

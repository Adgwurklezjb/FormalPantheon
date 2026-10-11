import Mathlib

/-!
Uniform right-grid integration for CDT v2, supplied TeX 4150-4228.
Meanings and endpoint checks precede these bodies in
-/

namespace DirichletL

theorem abs_sum_right_grid_sub_integral_le_of_cell_bound {f : ℝ → ℝ}
    {n : ℕ} (hn : 0 < n) {ξ : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1)
    (hcell : ∀ i : Fin n, ∀ x ∈ Set.Icc ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n),
      |f (((i.val : ℝ) + 1) / n) - f x| ≤ ξ) :
    |(∑ i : Fin n, f (((i.val : ℝ) + 1) / n)) / n - ∫ x in (0 : ℝ)..1, f x| ≤ ξ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let a (k : ℕ) : ℝ := (k : ℝ) / n
  have hstep (k : ℕ) : a (k + 1) - a k = 1 / (n : ℝ) := by
    dsimp only [a]
    push_cast
    ring
  have hzero (k : ℕ) : 0 ≤ a k := div_nonneg (Nat.cast_nonneg _) hnR.le
  have hle (k : ℕ) : a k ≤ a (k + 1) := by
    apply sub_nonneg.mp
    rw [hstep]
    positivity
  have hone {k : ℕ} (hk : k < n) : a (k + 1) ≤ 1 := by
    apply (div_le_one hnR).mpr
    exact_mod_cast Nat.succ_le_of_lt hk
  have hint {k : ℕ} (hk : k < n) :
      IntervalIntegrable f MeasureTheory.volume (a k) (a (k + 1)) := by
    apply hf.mono_set
    rw [Set.uIcc_of_le (hle k), Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact Set.Icc_subset_Icc (hzero k) (hone hk)
  have hcellint (k : ℕ) (hk : k < n) :
      |f (a (k + 1)) / n - ∫ x in a k..a (k + 1), f x| ≤ ξ / n := by
    have hbound : ∀ x ∈ Set.uIoc (a k) (a (k + 1)),
        ‖f (a (k + 1)) - f x‖ ≤ ξ := by
      intro x hx
      rw [Set.uIoc_of_le (hle k)] at hx
      have hx' : x ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n) := by
        simpa only [a, Nat.cast_add, Nat.cast_one] using Set.Ioc_subset_Icc_self hx
      simpa only [a, Nat.cast_add, Nat.cast_one, Real.norm_eq_abs] using
        hcell ⟨k, hk⟩ x hx'
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    have hconst : (∫ _ in a k..a (k + 1), f (a (k + 1))) = f (a (k + 1)) / n := by
      rw [intervalIntegral.integral_const, hstep, smul_eq_mul]
      ring
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hint hk), hconst,
      Real.norm_eq_abs, hstep, abs_of_nonneg (one_div_nonneg.mpr hnR.le)] at h
    simpa only [one_div, div_eq_mul_inv, one_mul] using h
  have htel := intervalIntegral.sum_integral_adjacent_intervals
    (a := a) (n := n) (fun k hk => hint hk)
  have ha0 : a 0 = 0 := by simp [a]
  have han : a n = 1 := by simp [a, hnR.ne']
  rw [ha0, han] at htel
  calc
    _ = |∑ k ∈ Finset.range n,
        (f (a (k + 1)) / n - ∫ x in a k..a (k + 1), f x)| := by
      rw [Finset.sum_sub_distrib, htel, ← Finset.sum_div, Finset.sum_range]
      simp only [a, Nat.cast_add, Nat.cast_one]
    _ ≤ ∑ k ∈ Finset.range n,
        |f (a (k + 1)) / n - ∫ x in a k..a (k + 1), f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, ξ / (n : ℝ) :=
      Finset.sum_le_sum (fun k hk => hcellint k (Finset.mem_range.mp hk))
    _ = ξ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hnR.ne']

theorem abs_sum_right_grid_sub_integral_le {f : ℝ → ℝ} {n : ℕ} (hn : 0 < n)
    {ξ η : ℝ} (hf : IntervalIntegrable f MeasureTheory.volume 0 1)
    (hmesh : 1 / (n : ℝ) ≤ η)
    (hclose : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |x - y| ≤ η → |f x - f y| ≤ ξ) :
    |(∑ i : Fin n, f (((i.val : ℝ) + 1) / n)) / n - ∫ x in (0 : ℝ)..1, f x| ≤ ξ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply abs_sum_right_grid_sub_integral_le_of_cell_bound hn hf
  intro i x hx
  have hr : ((i.val : ℝ) + 1) / n ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, (div_le_one hnR).mpr ?_⟩
    exact_mod_cast Nat.succ_le_of_lt i.isLt
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(div_nonneg (Nat.cast_nonneg _) hnR.le).trans hx.1, hx.2.trans hr.2⟩
  apply hclose _ hr x hx'
  calc
    _ = ((i.val : ℝ) + 1) / n - x := abs_of_nonneg (sub_nonneg.mpr hx.2)
    _ ≤ ((i.val : ℝ) + 1) / n - (i.val : ℝ) / n := sub_le_sub_left hx.1 _
    _ = 1 / (n : ℝ) := by ring
    _ ≤ η := hmesh

end DirichletL

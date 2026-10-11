import Analysis.IntervalDiscrepancy

/-!
Finite signed rearrangement estimates for CDT v2, supplied TeX 4130-4228.
The regular grid uses right endpoints. Declaration meanings and sign checks
-/

namespace DirichletL

open scoped BigOperators

theorem sum_mul_le_sum_mul_sort {d : ℕ} (f g : Fin d → ℝ) :
    ∑ i, f i * g i ≤ ∑ i, f (Tuple.sort f i) * g (Tuple.sort g i) := by
  calc
    _ = ∑ i, f (Tuple.sort f i) * g (Tuple.sort f i) :=
      (Equiv.sum_comp (Tuple.sort f) (fun i => f i * g i)).symm
    _ ≤ _ := by
      simpa only [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply] using
        ((Tuple.monotone_sort f).monovary (Tuple.monotone_sort g)).sum_mul_comp_perm_le_sum_mul
          (σ := (Tuple.sort f).trans (Tuple.sort g).symm)

/-- Increasingly sorted values weighted by the right endpoints of a uniform finite grid. -/
noncomputable def sortedGridSum {d : ℕ} (a : Fin d → ℝ) : ℝ :=
  ∑ i, (((i.val : ℝ) + 1) / d) * a (Tuple.sort a i)

theorem abs_sortedGridSum_le {d : ℕ} (a : Fin d → ℝ) {B : ℝ}
    (hB : ∀ i, |a i| ≤ B) : |sortedGridSum a| ≤ d * B := by
  calc
    _ ≤ ∑ i, |(((i.val : ℝ) + 1) / d) * a (Tuple.sort a i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin d, B := by
      apply Finset.sum_le_sum
      intro i _
      have hd : 0 < (d : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
      have hi : (i.val : ℝ) + 1 ≤ d := by exact_mod_cast (Nat.succ_le_of_lt i.isLt)
      have h0 : 0 ≤ ((i.val : ℝ) + 1) / d := by positivity
      have h1 : ((i.val : ℝ) + 1) / d ≤ 1 := (div_le_one hd).mpr hi
      rw [abs_mul, abs_of_nonneg h0]
      exact (mul_le_of_le_one_left (abs_nonneg _) h1).trans (hB _)
    _ = d * B := by simp

theorem HasIntervalDiscrepancyLE.abs_coordinate_sub_grid_le {d : ℕ}
    {t : Fin d → ℝ} {ε : ℝ} (h : HasIntervalDiscrepancyLE t ε)
    (hcube : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) (hmono : Monotone t) (i : Fin d) :
    |t i - ((i.val : ℝ) + 1) / d| ≤ ε := by
  have hL := h.coordinate_lower hcube hmono i
  have hU := h.coordinate_upper hcube hmono i
  simp only [Nat.cast_add, Nat.cast_one] at hL
  have hi : (i.val : ℝ) / d ≤ ((i.val : ℝ) + 1) / d :=
    div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg d)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem HasIntervalDiscrepancyLE.sum_mul_le_sortedGridSum {d : ℕ}
    {t : Fin d → ℝ} {ε : ℝ} (h : HasIntervalDiscrepancyLE t ε)
    (hcube : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) (a : Fin d → ℝ) {B : ℝ}
    (hB : ∀ i, |a i| ≤ B) :
    ∑ i, t i * a i ≤ sortedGridSum a + d * ε * B := by
  have hs := h.comp_perm (Tuple.sort t)
  have hcube' : ∀ i, (t ∘ Tuple.sort t) i ∈ Set.Icc (0 : ℝ) 1 :=
    fun i => hcube (Tuple.sort t i)
  calc
    _ ≤ ∑ i, t (Tuple.sort t i) * a (Tuple.sort a i) := sum_mul_le_sum_mul_sort t a
    _ ≤ ∑ i, ((((i.val : ℝ) + 1) / d) * a (Tuple.sort a i) + ε * B) := by
      apply Finset.sum_le_sum
      intro i _
      have he := hs.abs_coordinate_sub_grid_le hcube' (Tuple.monotone_sort t) i
      have hε : 0 ≤ ε := (abs_nonneg _).trans he
      have herr : (t (Tuple.sort t i) - ((i.val : ℝ) + 1) / d) *
          a (Tuple.sort a i) ≤ ε * B := by
        calc
          _ ≤ |(t (Tuple.sort t i) - ((i.val : ℝ) + 1) / d) *
              a (Tuple.sort a i)| := le_abs_self _
          _ = |t (Tuple.sort t i) - ((i.val : ℝ) + 1) / d| *
              |a (Tuple.sort a i)| := abs_mul _ _
          _ ≤ ε * B := mul_le_mul he (hB _) (abs_nonneg _) hε
      linarith
    _ = _ := by simp [sortedGridSum, Finset.sum_add_distrib, mul_assoc]

end DirichletL

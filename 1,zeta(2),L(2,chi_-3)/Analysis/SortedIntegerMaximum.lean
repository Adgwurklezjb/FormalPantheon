import Analysis.IntegerWeightedMaximum

/-!
Sorting and scaling CDT's signed finite majorant, supplied TeX 3503-3538, 8384-8404.
-/

namespace DirichletL

open scoped BigOperators

/-- Sort whole bound/mass pairs and accumulate their mass and signed maximum numerator. -/
def sortedIntegerMaximum (entries : List (ℤ × ℤ)) : ℤ × ℤ :=
  integerMaximumFold (entries.mergeSort (fun entry other => decide (entry.1 ≤ other.1))) 0 0

theorem sortedIntegerMaximum_fst (entries : List (ℤ × ℤ)) :
    (sortedIntegerMaximum entries).1 = (entries.map Prod.snd).sum := by
  rw [sortedIntegerMaximum, integerMaximumFold_fst, zero_add]
  exact ((List.mergeSort_perm entries _).map Prod.snd).sum_eq

theorem sortedIntegerMaximum_snd (entries : List (ℤ × ℤ)) :
    (sortedIntegerMaximum entries).2 = integerPairwiseMaximum entries := by
  have hs : (entries.mergeSort (fun entry other => decide (entry.1 ≤ other.1))).Pairwise
      (fun entry other => entry.1 ≤ other.1) := by
    have hb := List.sorted_mergeSort (le := fun entry other : ℤ × ℤ =>
      decide (entry.1 ≤ other.1))
      (fun a b c hab hbc => by
        simpa only [decide_eq_true_eq] using
          le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
      (fun a b => by
        simpa only [Bool.or_eq_true, decide_eq_true_eq] using le_total a.1 b.1) entries
    simpa only [decide_eq_true_eq] using hb
  rw [sortedIntegerMaximum, integerMaximumFold_zero_snd _ hs]
  exact integerPairwiseMaximum_perm (List.mergeSort_perm entries _)

theorem weightedPairwiseMaxSum_eq_integerPairwiseMaximum
    (entries : List (ℤ × ℤ)) {D L : ℝ} (hD : 0 < D) (hL : 0 < L) :
    weightedPairwiseMaxSum
      (fun i : Fin entries.length => (entries[i.1].1 : ℝ) / D)
      (fun i : Fin entries.length => (entries[i.1].2 : ℝ) / L) =
        (integerPairwiseMaximum entries : ℝ) / (D * L ^ 2) := by
  have hterm (entry other : ℤ × ℤ) :
      (entry.2 : ℝ) / L * ((other.2 : ℝ) / L) *
        max ((entry.1 : ℝ) / D) ((other.1 : ℝ) / D) =
          ((entry.2 * other.2 * max entry.1 other.1 : ℤ) : ℝ) / (D * L ^ 2) := by
    rw [max_div_div_right hD.le]
    simp only [Int.cast_mul, Int.cast_max]
    field_simp [hD.ne', hL.ne']
  have hsum : (∑ i : Fin entries.length, ∑ j : Fin entries.length,
      entries[i.1].2 * entries[j.1].2 * max entries[i.1].1 entries[j.1].1) =
      integerPairwiseMaximum entries := by
    calc
      _ = ∑ i : Fin entries.length,
          (entries.map (fun other =>
            entries[i.1].2 * other.2 * max entries[i.1].1 other.1)).sum := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Fin.sum_univ_fun_getElem entries
          (fun other => entries[i.1].2 * other.2 * max entries[i.1].1 other.1)
      _ = _ := Fin.sum_univ_fun_getElem entries
        (fun entry => (entries.map (fun other =>
          entry.2 * other.2 * max entry.1 other.1)).sum)
  unfold weightedPairwiseMaxSum
  simp_rw [hterm]
  calc
    _ = (∑ i : Fin entries.length, ∑ j : Fin entries.length,
        ((entries[i.1].2 * entries[j.1].2 *
          max entries[i.1].1 entries[j.1].1 : ℤ) : ℝ)) / (D * L ^ 2) := by
      simp only [Finset.sum_div]
    _ = ((∑ i : Fin entries.length, ∑ j : Fin entries.length,
        entries[i.1].2 * entries[j.1].2 *
          max entries[i.1].1 entries[j.1].1 : ℤ) : ℝ) / (D * L ^ 2) := by
      simp only [Int.cast_sum]
    _ = _ := by rw [hsum]

theorem weightedPairwiseMaxSum_eq_sortedIntegerMaximum
    (entries : List (ℤ × ℤ)) {D L : ℝ} (hD : 0 < D) (hL : 0 < L) :
    weightedPairwiseMaxSum
      (fun i : Fin entries.length => (entries[i.1].1 : ℝ) / D)
      (fun i : Fin entries.length => (entries[i.1].2 : ℝ) / L) =
        ((sortedIntegerMaximum entries).2 : ℝ) / (D * L ^ 2) := by
  rw [weightedPairwiseMaxSum_eq_integerPairwiseMaximum entries hD hL,
    sortedIntegerMaximum_snd]

end DirichletL

import Analysis.FiniteRearrangement
import Analysis.VandermondeCircleBound

/-!
Finite maximum-sum identity behind the signed grid limit in CDT v2,
TeX 1154-1202 and 3503-3540. The diagonal term and sign checks are recorded
-/

namespace DirichletL

open scoped BigOperators

/-- The signed pairwise maximum sum of a finite family of real values. -/
def pairwiseMaxSum {d : ℕ} (a : Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, max (a i) (a j)

theorem two_mul_mul_sortedGridSum_eq_pairwiseMaxSum_add_sum {d : ℕ}
    (a : Fin d → ℝ) :
    2 * d * sortedGridSum a = pairwiseMaxSum a + ∑ i, a i := by
  let e := Tuple.sort a
  let g (i j : Fin d) : ℝ := max (a (e i)) (a (e j))
  have hsym : ∀ i j, g i j = g j i := by
    intro i j
    simp only [g, max_comm]
  have hdecomp := sum_sum_eq_diag_add_two_mul_sum_Ioi g hsym
  have hsorted (i j : Fin d) (hij : i < j) : g i j = a (e j) := by
    dsimp only [g]
    rw [max_eq_right]
    exact Tuple.monotone_sort a hij.le
  have hoff : (∑ i, ∑ j ∈ Finset.Ioi i, g i j) =
      ∑ j, (j.val : ℝ) * a (e j) := by
    calc
      (∑ i, ∑ j ∈ Finset.Ioi i, g i j) =
          ∑ i, ∑ j ∈ Finset.Ioi i, a (e j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hsorted i j (Finset.mem_Ioi.mp hj)
      _ = ∑ j, ∑ i ∈ Finset.Iio j, a (e j) := by
        simp_rw [show ∀ i, (∑ j ∈ Finset.Ioi i, a (e j)) =
          ∑ j, if i < j then a (e j) else 0 by
          intro i
          have hIoi : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by
            ext j
            simp [Finset.mem_Ioi]
          rw [hIoi]
          simpa using (Finset.sum_filter (s := (Finset.univ : Finset (Fin d)))
            (p := fun j : Fin d => i < j) (fun j => a (e j)))]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        have hIio : Finset.Iio j = Finset.univ.filter (fun i => i < j) := by
          ext i
          simp [Finset.mem_Iio]
        rw [hIio]
        simpa using (Finset.sum_filter (s := (Finset.univ : Finset (Fin d)))
          (p := fun i : Fin d => i < j) (fun _ => a (e j))).symm
      _ = ∑ j, (j.val : ℝ) * a (e j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_const, Fin.card_Iio]
        simp only [nsmul_eq_mul]
  have hdiag : (∑ i, g i i) = ∑ i, a (e i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [g, max_self]
  have hpair : pairwiseMaxSum a = (∑ i, a (e i)) +
      2 * ∑ i, (i.val : ℝ) * a (e i) := by
    rw [pairwiseMaxSum]
    have hreindex : (∑ i, ∑ j, max (a i) (a j)) = ∑ i, ∑ j, g i j := by
      dsimp only [g, e]
      rw [← Equiv.sum_comp (Tuple.sort a) (fun i => ∑ j, max (a i) (a j))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Equiv.sum_comp (Tuple.sort a) (fun j => max (a (e i)) (a j))]
    rw [hreindex, hdecomp, hdiag, hoff]
  by_cases hd : d = 0
  · subst d
    simp [sortedGridSum, pairwiseMaxSum]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hsum : (∑ i, a (e i)) = ∑ i, a i := by
    dsimp only [e]
    exact Equiv.sum_comp (Tuple.sort a) a
  have hterm (i : Fin d) :
      2 * (d : ℝ) * (((i.val : ℝ) + 1) / d * a (e i)) =
        2 * a (e i) + 2 * (i.val : ℝ) * a (e i) := by
    field_simp
    ring
  calc
    2 * (d : ℝ) * sortedGridSum a =
        ∑ i, 2 * (d : ℝ) * (((i.val : ℝ) + 1) / d * a (e i)) := by
      unfold sortedGridSum
      rw [Finset.mul_sum]
    _ = 2 * ∑ i, a (e i) + 2 * ∑ i, (i.val : ℝ) * a (e i) := by
      calc
        _ = ∑ i, (2 * a (e i) + 2 * (i.val : ℝ) * a (e i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hterm i
        _ = (∑ i, 2 * a (e i)) + (∑ i, 2 * (i.val : ℝ) * a (e i)) :=
          Finset.sum_add_distrib
        _ = _ := by
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ = pairwiseMaxSum a + ∑ i, a i := by
      rw [hpair, hsum]
      ring

theorem abs_two_mul_sortedGridSum_div_sub_pairwiseMaxSum_div_sq_le {d : ℕ}
    (hd : 0 < d) (a : Fin d → ℝ) {B : ℝ} (hB : ∀ i, |a i| ≤ B) :
    |2 * sortedGridSum a / d - pairwiseMaxSum a / (d : ℝ) ^ 2| ≤ B / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsum : |∑ i, a i| ≤ (d : ℝ) * B := by
    calc
      _ ≤ ∑ i, |a i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin d, B := Finset.sum_le_sum (fun i _ => hB i)
      _ = _ := by simp
  have hid : 2 * sortedGridSum a / d - pairwiseMaxSum a / (d : ℝ) ^ 2 =
      (∑ i, a i) / (d : ℝ) ^ 2 := by
    have hs : 2 * sortedGridSum a = (pairwiseMaxSum a + ∑ i, a i) / (d : ℝ) := by
      apply (eq_div_iff hdR.ne').mpr
      nlinarith [two_mul_mul_sortedGridSum_eq_pairwiseMaxSum_add_sum a]
    rw [hs]
    simp only [add_div, div_div, ← pow_two]
    ring
  rw [hid, abs_div, abs_of_pos (sq_pos_of_pos hdR)]
  calc
    _ ≤ ((d : ℝ) * B) / (d : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hsum (sq_nonneg _)
    _ = B / d := by field_simp

end DirichletL

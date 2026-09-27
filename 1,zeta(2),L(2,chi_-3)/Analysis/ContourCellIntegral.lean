import Analysis.ContourMap
import Analysis.TwoRadiusHolonomy
import Analysis.PairwiseMaximumCellBound
import Analysis.WeightedPairwiseMaximum

/-!
Cell majorants for CDT's signed two-radius integral, supplied TeX 3503-3538 and 8384-8404.
-/

namespace DirichletL

open scoped BigOperators

theorem continuous_circleLogProfile_cdtContourMap {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    Continuous (circleLogProfile (fun z => cdtContourMap ((r : ℂ) * z))) := by
  have hn (z : ℂ) : ‖(r : ℂ) * z‖ = r * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hm : Set.MapsTo (fun z : ℂ => (r : ℂ) * z)
      (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    rw [Metric.mem_closedBall, dist_zero_right, hn]
    exact (mul_le_mul_of_nonneg_left hz1 hr.le).trans (by simpa only [mul_one] using hr1)
  apply continuous_circleLogProfile
    (analyticOnNhd_cdtContourMap.continuousOn.comp
      (continuous_const.mul continuous_id).continuousOn hm)
  intro z hz hzero
  have hz1 : ‖(r : ℂ) * z‖ ≤ 1 := by simpa only [hn, hz, mul_one] using hr1
  have hprod := (cdtContourMap_eq_zero_iff hz1).mp hzero
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hzC : z ≠ 0 := norm_ne_zero_iff.mp (by simpa only [hz] using one_ne_zero)
  exact mul_ne_zero hrC hzC hprod

theorem twoRadiusMaxIntegral_le_weightedCellSum (ψ : ℂ → ℂ) (r p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hf : Continuous (circleLogProfile (fun z => ψ ((r : ℂ) * z))))
    (hg : Continuous (circleLogProfile ψ)) {n m : ℕ} (a b A B : ℕ → ℝ)
    (ha0 : a 0 = 0) (han : a n = 1) (hb0 : b 0 = 0) (hbm : b m = 1)
    (ha : ∀ i < n, a i ≤ a (i + 1)) (hb : ∀ j < m, b j ≤ b (j + 1))
    (hA : ∀ i < n, ∀ x ∈ Set.Icc (a i) (a (i + 1)),
      circleLogProfile (fun z => ψ ((r : ℂ) * z)) x ≤ A i)
    (hB : ∀ j < m, ∀ y ∈ Set.Icc (b j) (b (j + 1)), circleLogProfile ψ y ≤ B j) :
    twoRadiusMaxIntegral ψ r p ≤
      weightedPairwiseMaxSum
        (Sum.elim (fun i : Fin n => A i.1) (fun j : Fin m => B j.1))
        (Sum.elim (fun i : Fin n => p * (a (i.1 + 1) - a i.1))
          (fun j : Fin m => (1 - p) * (b (j.1 + 1) - b j.1))) := by
  have hff := pairwiseMaxIntegral_le_sum_cell_bounds hf hf a a A A
    ha0 han ha0 han ha ha hA hA
  have hfg := pairwiseMaxIntegral_le_sum_cell_bounds hf hg a b A B
    ha0 han hb0 hbm ha hb hA hB
  have hgg := pairwiseMaxIntegral_le_sum_cell_bounds hg hg b b B B
    hb0 hbm hb0 hbm hb hb hB hB
  have hcross : 0 ≤ 2 * p * (1 - p) :=
    mul_nonneg (mul_nonneg (by norm_num) hp0) (sub_nonneg.mpr hp1)
  have hbound := add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hff (sq_nonneg p))
      (mul_le_mul_of_nonneg_left hfg hcross))
    (mul_le_mul_of_nonneg_left hgg (sq_nonneg (1 - p)))
  have hscale (s t : ℕ) (x y U V : ℕ → ℝ) (c d : ℝ) :
      c * d * (∑ i ∈ Finset.range s, ∑ j ∈ Finset.range t, x i * y j * max (U i) (V j)) =
        ∑ i : Fin s, ∑ j : Fin t, (c * x i.1) * (d * y j.1) * max (U i.1) (V j.1) := by
    simp only [Finset.sum_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hinner : p ^ 2 *
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (a (i + 1) - a i) * (a (j + 1) - a j) * max (A i) (A j)) =
      weightedPairwiseMaxSum (fun i : Fin n => A i.1)
        (fun i : Fin n => p * (a (i.1 + 1) - a i.1)) := by
    rw [pow_two]
    exact hscale n n (fun i => a (i + 1) - a i) (fun i => a (i + 1) - a i) A A p p
  have houter : (1 - p) ^ 2 *
      (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
        (b (i + 1) - b i) * (b (j + 1) - b j) * max (B i) (B j)) =
      weightedPairwiseMaxSum (fun j : Fin m => B j.1)
        (fun j : Fin m => (1 - p) * (b (j.1 + 1) - b j.1)) := by
    rw [pow_two]
    exact hscale m m (fun i => b (i + 1) - b i) (fun i => b (i + 1) - b i) B B
      (1 - p) (1 - p)
  have hmixed : (2 * p * (1 - p)) *
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
        (a (i + 1) - a i) * (b (j + 1) - b j) * max (A i) (B j)) =
      2 * (∑ i : Fin n, ∑ j : Fin m,
        (p * (a (i.1 + 1) - a i.1)) * ((1 - p) * (b (j.1 + 1) - b j.1)) *
          max (A i.1) (B j.1)) := by
    rw [mul_assoc (2 : ℝ) p (1 - p), mul_assoc]
    exact congrArg (fun x : ℝ => 2 * x)
      (hscale n m (fun i => a (i + 1) - a i) (fun j => b (j + 1) - b j) A B p (1 - p))
  rw [hinner, hmixed, houter] at hbound
  rw [weightedPairwiseMaxSum_sum_elim]
  exact hbound

end DirichletL

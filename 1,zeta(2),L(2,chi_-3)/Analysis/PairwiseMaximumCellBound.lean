import Analysis.AdaptiveCellIntegral
import Analysis.PairwiseMaximumIntegral

/-!
Adaptive cell majorants for CDT v2's maximum integral, supplied TeX 3503-3538.
Meanings and the two independent partitions precede these bodies in
-/

namespace DirichletL

open scoped BigOperators

theorem pairwiseMaxIntegral_le_sum_cell_bounds {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) {n m : ℕ} (a b A B : ℕ → ℝ)
    (ha0 : a 0 = 0) (han : a n = 1) (hb0 : b 0 = 0) (hbm : b m = 1)
    (ha : ∀ i < n, a i ≤ a (i + 1)) (hb : ∀ j < m, b j ≤ b (j + 1))
    (hA : ∀ i < n, ∀ x ∈ Set.Icc (a i) (a (i + 1)), f x ≤ A i)
    (hB : ∀ j < m, ∀ y ∈ Set.Icc (b j) (b (j + 1)), g y ≤ B j) :
    pairwiseMaxIntegral f g ≤
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
        (a (i + 1) - a i) * (b (j + 1) - b j) * max (A i) (B j) := by
  let J (x : ℝ) : ℝ := ∫ y in (0 : ℝ)..1, max (f x) (g y)
  let U (i : ℕ) : ℝ := ∑ j ∈ Finset.range m, (b (j + 1) - b j) * max (A i) (B j)
  have hJ : Continuous J := (lipschitzWith_integral_max hg.continuousOn).continuous.comp hf
  have hU : ∀ i < n, ∀ x ∈ Set.Icc (a i) (a (i + 1)), J x ≤ U i := by
    intro i hi x hx
    have h := integral_le_sum_cell_upper_bounds
      (f := fun y => max (f x) (g y)) (n := m) b (fun j => max (A i) (B j)) hb
      (fun j _ => (continuous_const.sup hg).intervalIntegrable (b j) (b (j + 1)))
      (fun j hj y hy => max_le_max (hA i hi x hx) (hB j hj y hy))
    simpa only [hb0, hbm] using h
  have houter := integral_le_sum_cell_upper_bounds a U ha
    (fun i _ => hJ.intervalIntegrable (a i) (a (i + 1))) hU
  rw [ha0, han] at houter
  change pairwiseMaxIntegral f g ≤
    ∑ i ∈ Finset.range n, (a (i + 1) - a i) * U i at houter
  calc
    _ ≤ ∑ i ∈ Finset.range n, (a (i + 1) - a i) * U i := houter
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [U]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

end DirichletL

import Mathlib

/-!
Finite cell majorants for CDT v2's signed integral, supplied TeX 3503-3538.
Meanings and endpoint checks precede these bodies in
-/

namespace DirichletL

open scoped BigOperators

theorem integral_le_sum_cell_upper_bounds {f : ℝ → ℝ} {n : ℕ}
    (a B : ℕ → ℝ) (ha : ∀ i < n, a i ≤ a (i + 1))
    (hf : ∀ i < n, IntervalIntegrable f MeasureTheory.volume (a i) (a (i + 1)))
    (hB : ∀ i < n, ∀ x ∈ Set.Icc (a i) (a (i + 1)), f x ≤ B i) :
    (∫ x in (a 0)..(a n), f x) ≤
      ∑ i ∈ Finset.range n, (a (i + 1) - a i) * B i := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hf]
  apply Finset.sum_le_sum
  intro i hi
  have hin := Finset.mem_range.mp hi
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using
    intervalIntegral.integral_mono_on (ha i hin) (hf i hin)
      intervalIntegrable_const (hB i hin)

end DirichletL

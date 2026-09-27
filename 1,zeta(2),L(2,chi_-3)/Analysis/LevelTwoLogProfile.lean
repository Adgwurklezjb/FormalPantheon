import Analysis.LevelTwoLogTail
import Arithmetic.QBinomial

/-!
The finite product for CDT v2's logarithmic contour estimate, TeX 6947-6948 and 8384-8404.
-/

namespace DirichletL

theorem qPochhammer_neg_ne_zero (N : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammer (-q) q N ≠ 0 := by
  unfold qPochhammer
  apply Finset.prod_ne_zero_iff.mpr
  intro n _
  rw [neg_mul, sub_neg_eq_add, ← pow_succ']
  apply Complex.slitPlane_ne_zero
  apply Complex.mem_slitPlane_of_norm_lt_one
  rw [norm_pow]
  exact (pow_le_pow_of_le_one (norm_nonneg q) hq.le
    (show 1 ≤ n + 1 by omega)).trans_lt (by simpa only [pow_one] using hq)

theorem levelTwoLogPartial_eq_log_normSq_qPochhammer (N : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    levelTwoLogPartial N q = 8 * Real.log 2 +
      (1 / 2) * Real.log (Complex.normSq q) +
      12 * Real.log (Complex.normSq (qPochhammer (-q) q N)) := by
  have hne : ∀ n ∈ Finset.range N, 1 - -q * q ^ n ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mp (qPochhammer_neg_ne_zero N hq)
  have hlog : Real.log ‖qPochhammer (-q) q N‖ =
      ∑ n ∈ Finset.range N, Real.log ‖1 + q ^ (n + 1)‖ := by
    rw [qPochhammer, norm_prod, Real.log_prod _ _ (fun n hn => norm_ne_zero_iff.mpr (hne n hn))]
    simp only [neg_mul, sub_neg_eq_add, pow_succ']
  rw [levelTwoLogPartial_eq_real]
  simp_rw [Complex.normSq_eq_norm_sq, Real.log_pow, Nat.cast_ofNat]
  rw [hlog, ← Finset.mul_sum]
  ring

end DirichletL

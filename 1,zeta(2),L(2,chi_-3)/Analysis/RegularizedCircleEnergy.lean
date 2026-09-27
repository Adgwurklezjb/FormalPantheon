import Comparator.Statement

/-!
The regularized circle energy used for CDT v2, supplied TeX 4054-4067,
and published UDC Lemma 2.5.9. The independent verification, implementation
deviation, and declaration meanings precede these proofs in
-/

namespace DirichletL

open scoped ComplexConjugate

theorem norm_sq_one_sub_real_mul_mul_conj {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (r : ℝ) :
    ‖1 - (r : ℂ) * (z * conj w)‖ ^ 2 = r * ‖z - w‖ ^ 2 + (1 - r) ^ 2 := by
  have hzs : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz, one_pow]
  have hws : Complex.normSq w = 1 := by rw [Complex.normSq_eq_norm_sq, hw, one_pow]
  simp [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_mul,
    hzs, hws, Complex.mul_re]
  ring

theorem log_norm_sub_le_log_norm_regularized {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hzw : z ≠ w) {r : ℝ} (hr : 0 < r) :
    Real.log ‖z - w‖ ≤ Real.log ‖1 - (r : ℂ) * (z * conj w)‖ - Real.log r / 2 := by
  have hnorm : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
  have hbound : r * ‖z - w‖ ^ 2 ≤ ‖1 - (r : ℂ) * (z * conj w)‖ ^ 2 := by
    rw [norm_sq_one_sub_real_mul_mul_conj hz hw]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hlog := Real.log_le_log (mul_pos hr (sq_pos_of_pos hnorm)) hbound
  rw [Real.log_mul hr.ne' (pow_ne_zero _ hnorm.ne'), Real.log_pow, Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

theorem hasSum_regularized_circle_energy {ι : Type*} [Fintype ι] (z : ι → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => r ^ n / (n : ℝ) * ‖∑ i, z i ^ n‖ ^ 2)
      (-∑ i, ∑ j, Real.log ‖1 - (r : ℂ) * (z i * conj (z j))‖) := by
  have hs (i j : ι) := Complex.hasSum_taylorSeries_neg_log
    (z := (r : ℂ) * (z i * conj (z j))) (by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
        Complex.norm_conj, hz i, hz j, one_mul, mul_one] using hr1)
  have hsum := hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_sum (s := Finset.univ) (fun j _ => hs i j))
  have hterm (n : ℕ) :
      (∑ i, ∑ j, ((r : ℂ) * (z i * conj (z j))) ^ n / (n : ℂ)).re =
        r ^ n / (n : ℝ) * ‖∑ i, z i ^ n‖ ^ 2 := by
    have hc : (∑ i, ∑ j, ((r : ℂ) * (z i * conj (z j))) ^ n / (n : ℂ)) =
        ((r ^ n / (n : ℝ) : ℝ) : ℂ) * ((∑ i, z i ^ n) * conj (∑ j, z j ^ n)) := by
      simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast,
        map_sum, Finset.mul_sum, Finset.sum_mul, mul_pow, map_pow]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hc, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  convert Complex.hasSum_re hsum using 1
  · ext n
    exact (hterm n).symm
  · simp [Complex.log_re]

theorem fourier_mode_le_regularized_circle_energy {ι : Type*} [Fintype ι] (z : ι → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (m : ℕ) :
    r ^ m / (m : ℝ) * ‖∑ i, z i ^ m‖ ^ 2 ≤
      -∑ i, ∑ j, Real.log ‖1 - (r : ℂ) * (z i * conj (z j))‖ := by
  have hs := hasSum_regularized_circle_energy z hz hr hr1
  simpa only [hs.tsum_eq] using hs.summable.le_tsum m
    (fun j _ => mul_nonneg (div_nonneg (pow_nonneg hr _) (Nat.cast_nonneg _)) (sq_nonneg _))

end DirichletL

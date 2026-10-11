import Analysis.ReciprocalCubeSummation

/-!
The Fourier expansion of the integer reciprocal-cube sum on the upper
half plane. Its exact constant supplies the weight-three Eisenstein
numerator normalizations in CDT v2, Section 11.1. The source, convergence,
-/

namespace DirichletL

open Filter
open scoped Topology

private theorem hasSum_sq_mul_geometric {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (n : ℂ) ^ 2 * q ^ n) (q * (1 + q) / (1 - q) ^ 3) := by
  have h := (((hasSum_choose_mul_geometric_of_norm_lt_one 2 hq).mul_left 2).sub
    ((hasSum_choose_mul_geometric_of_norm_lt_one 1 hq).mul_left 3)).add
      (hasSum_geometric_of_norm_lt_one hq)
  have hne : 1 - q ≠ 0 :=
    sub_ne_zero.mpr (ne_of_apply_ne norm (by simpa using hq.ne'))
  convert h using 1
  · ext n
    rw [Nat.cast_choose_two]
    simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  · norm_num
    field_simp [hne]
    ring

private theorem cotangent_eq_exp_rational {z : ℂ} (hz : 0 < z.im) :
    Real.pi * Complex.cot (Real.pi * z) = (Real.pi : ℂ) * Complex.I -
      2 * Real.pi * Complex.I / (1 - Complex.exp (2 * Real.pi * Complex.I * z)) := by
  have hq := UpperHalfPlane.norm_exp_two_pi_I_lt_one (UpperHalfPlane.mk z hz)
  have h := pi_mul_cot_pi_q_exp (UpperHalfPlane.mk z hz)
  rw [tsum_geometric_of_norm_lt_one hq] at h
  simpa only [div_eq_mul_inv] using h

private theorem hasDerivAt_pi_mul_cot_pi {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (fun w : ℂ => Real.pi * Complex.cot (Real.pi * w))
      (4 * (Real.pi : ℂ) ^ 2 * Complex.exp (2 * Real.pi * Complex.I * z) /
        (1 - Complex.exp (2 * Real.pi * Complex.I * z)) ^ 2) z := by
  let q : ℂ → ℂ := fun w => Complex.exp (2 * Real.pi * Complex.I * w)
  have hq : ‖q z‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one (UpperHalfPlane.mk z hz)
  have hne : 1 - q z ≠ 0 := by
    intro h
    have hq1 := sub_eq_zero.mp h
    rw [← hq1, norm_one] at hq
    exact lt_irrefl _ hq
  have hdq : HasDerivAt q (q z * (2 * Real.pi * Complex.I)) z := by
    simpa only [q, id_eq, mul_one] using
      ((hasDerivAt_id z).const_mul (2 * (Real.pi : ℂ) * Complex.I)).cexp
  have hd := (hasDerivAt_const z ((Real.pi : ℂ) * Complex.I)).sub
    ((hasDerivAt_const z (2 * (Real.pi : ℂ) * Complex.I)).div
      ((hasDerivAt_const z (1 : ℂ)).sub hdq) hne)
  have heq : (fun w : ℂ => Real.pi * Complex.cot (Real.pi * w)) =ᶠ[𝓝 z]
      (fun w => (Real.pi : ℂ) * Complex.I - 2 * Real.pi * Complex.I / (1 - q w)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz]
      with w hw using cotangent_eq_exp_rational hw
  convert hd.congr_of_eventuallyEq heq using 1
  simp only [q, Pi.sub_apply, id_eq]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem cotangent_second_derivative_eq_exp_rational {z : ℂ} (hz : 0 < z.im) :
    deriv (deriv (fun w : ℂ => Real.pi * Complex.cot (Real.pi * w))) z =
      8 * (Real.pi : ℂ) ^ 3 * Complex.I * Complex.exp (2 * Real.pi * Complex.I * z) *
        (1 + Complex.exp (2 * Real.pi * Complex.I * z)) /
        (1 - Complex.exp (2 * Real.pi * Complex.I * z)) ^ 3 := by
  let q : ℂ → ℂ := fun w => Complex.exp (2 * Real.pi * Complex.I * w)
  have hq : ‖q z‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one (UpperHalfPlane.mk z hz)
  have hne : 1 - q z ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h, norm_one] at hq
    exact lt_irrefl _ hq
  have heq : deriv (fun w : ℂ => Real.pi * Complex.cot (Real.pi * w)) =ᶠ[𝓝 z]
      (fun w => 4 * (Real.pi : ℂ) ^ 2 * q w / (1 - q w) ^ 2) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz]
      with w hw using (hasDerivAt_pi_mul_cot_pi hw).deriv
  have hdq : HasDerivAt q (q z * (2 * Real.pi * Complex.I)) z := by
    simpa only [q, id_eq, mul_one] using
      ((hasDerivAt_id z).const_mul (2 * (Real.pi : ℂ) * Complex.I)).cexp
  have hd := (hdq.const_mul (4 * (Real.pi : ℂ) ^ 2)).fun_div
    (((hasDerivAt_const z (1 : ℂ)).fun_sub hdq).fun_pow 2) (pow_ne_zero _ hne)
  rw [heq.deriv_eq, hd.deriv]
  change _ = 8 * (Real.pi : ℂ) ^ 3 * Complex.I * q z * (1 + q z) / (1 - q z) ^ 3
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, zero_sub]
  field_simp [hne]
  ring

theorem tsum_one_div_int_add_cube {z : ℂ} (hz : 0 < z.im) :
    (∑' n : ℤ, 1 / (z + n) ^ 3) =
      4 * (Real.pi : ℂ) ^ 3 * Complex.I *
        ∑' n : ℕ, (n : ℂ) ^ 2 * Complex.exp (2 * Real.pi * Complex.I * z) ^ n := by
  have hq : ‖Complex.exp (2 * Real.pi * Complex.I * z)‖ < 1 :=
    UpperHalfPlane.norm_exp_two_pi_I_lt_one (UpperHalfPlane.mk z hz)
  rw [(hasSum_sq_mul_geometric hq).tsum_eq]
  have h := cotangent_second_derivative_eq_tsum_cube hz
  rw [cotangent_second_derivative_eq_exp_rational hz] at h
  linear_combination -(1 / 2 : ℂ) * h

end DirichletL

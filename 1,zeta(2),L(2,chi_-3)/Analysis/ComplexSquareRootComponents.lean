import Mathlib

/-!
Component identities for the roots in CDT's slit and lune maps, v2 TeX 9956-9964
-/

namespace DirichletL

theorem two_mul_re_mul_im_cpow_inv_two (z : ℂ) :
    2 * (z ^ (2⁻¹ : ℂ)).re * (z ^ (2⁻¹ : ℂ)).im = z.im := by
  have h := congrArg Complex.im (Complex.cpow_ofNat_inv_pow z 2)
  simp only [pow_two, Complex.mul_im] at h
  nlinarith only [h]

theorem im_cpow_inv_two_eq_div {z : ℂ} (hz : (z ^ (2⁻¹ : ℂ)).re ≠ 0) :
    (z ^ (2⁻¹ : ℂ)).im = z.im / (2 * (z ^ (2⁻¹ : ℂ)).re) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) hz)).2
  nlinarith only [two_mul_re_mul_im_cpow_inv_two z]

theorem re_cpow_inv_two_eq_div {z : ℂ} (hz : (z ^ (2⁻¹ : ℂ)).im ≠ 0) :
    (z ^ (2⁻¹ : ℂ)).re = z.im / (2 * (z ^ (2⁻¹ : ℂ)).im) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) hz)).2
  nlinarith only [two_mul_re_mul_im_cpow_inv_two z]

end DirichletL

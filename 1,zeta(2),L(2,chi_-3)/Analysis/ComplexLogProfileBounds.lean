import Mathlib

/-!
Local logarithmic errors for CDT v2's finite contour profile, TeX 8384-8404.
Meanings and denominator checks precede these bodies in
-/

namespace DirichletL

theorem log_norm_sub_eq_re_log_one_add {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Real.log ‖b‖ - Real.log ‖a‖ = (Complex.log (1 + (b - a) / a)).re := by
  have heq : 1 + (b - a) / a = b / a := by field_simp; ring
  rw [heq, Complex.log_re, norm_div,
    Real.log_div (norm_ne_zero_iff.mpr hb) (norm_ne_zero_iff.mpr ha)]

theorem abs_log_norm_sub_sub_re_le {a b : ℂ} {β ε : ℝ}
    (hβ : β ≤ ‖a‖) (hε : ‖b - a‖ ≤ ε) (hsmall : ε < β) :
    |Real.log ‖b‖ - Real.log ‖a‖ - ((b - a) / a).re| ≤
      ε ^ 2 / (2 * β * (β - ε)) := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hβ0 : 0 < β := hε0.trans_lt hsmall
  have ha : a ≠ 0 := norm_pos_iff.mp (hβ0.trans_le hβ)
  have hb : b ≠ 0 := by
    intro hb
    have hbad : ‖a‖ ≤ ε := by simpa only [hb, zero_sub, norm_neg] using hε
    exact (not_le_of_gt (hsmall.trans_le hβ)) hbad
  have hratio : ε / β < 1 := (div_lt_one hβ0).mpr hsmall
  have hbound : ‖(b - a) / a‖ ≤ ε / β := by
    rw [norm_div]
    gcongr
  have hlt : ‖(b - a) / a‖ < 1 := hbound.trans_lt hratio
  rw [log_norm_sub_eq_re_log_one_add ha hb, ← Complex.sub_re]
  calc
    _ ≤ ‖Complex.log (1 + (b - a) / a) - (b - a) / a‖ := Complex.abs_re_le_norm _
    _ ≤ ‖(b - a) / a‖ ^ 2 * (1 - ‖(b - a) / a‖)⁻¹ / 2 :=
      Complex.norm_log_one_add_sub_self_le hlt
    _ ≤ (ε / β) ^ 2 * (1 - ε / β)⁻¹ / 2 := by
      gcongr
      · exact inv_nonneg.mpr (sub_nonneg.mpr hlt.le)
      · exact sub_pos.mpr hratio
    _ = ε ^ 2 / (2 * β * (β - ε)) := by
      field_simp [hβ0.ne', (sub_pos.mpr hsmall).ne', (sub_pos.mpr hratio).ne']

end DirichletL

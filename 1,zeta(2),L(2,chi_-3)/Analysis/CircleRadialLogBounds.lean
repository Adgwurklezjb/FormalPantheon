import Mathlib

/-!
Exact radial distance bounds for CDT v2, supplied TeX 4150-4153.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace DirichletL

theorem radial_circle_norm_sub_sq {u a : ℂ} (hu : ‖u‖ = 1) (ha : ‖a‖ = 1) (r : ℝ) :
    ‖(r : ℂ) * u - a‖ ^ 2 = r * ‖u - a‖ ^ 2 + (1 - r) ^ 2 := by
  have hu' : Complex.normSq u = 1 := by rw [Complex.normSq_eq_norm_sq, hu, one_pow]
  have ha' : Complex.normSq a = 1 := by rw [Complex.normSq_eq_norm_sq, ha, one_pow]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_mul,
    Complex.normSq_ofReal, hu', ha', mul_one, mul_assoc, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem radial_circle_distance_bounds {u a : ℂ} (hu : ‖u‖ = 1) (ha : ‖a‖ = 1)
    {r : ℝ} (hr : (1 / 2 : ℝ) ≤ r) (hr1 : r ≤ 1) :
    ‖u - a‖ / 2 ≤ ‖(r : ℂ) * u - a‖ ∧ ‖(r : ℂ) * u - a‖ ≤ 2 := by
  have hid := radial_circle_norm_sub_sq hu ha r
  have hscaled : 0 ≤ (r - 1 / 4) * ‖u - a‖ ^ 2 :=
    mul_nonneg (by linarith only [hr]) (sq_nonneg _)
  have hr0 : 0 ≤ r := by linarith only [hr]
  constructor
  · nlinarith only [hid, hscaled, sq_nonneg (1 - r),
      norm_nonneg (u - a), norm_nonneg ((r : ℂ) * u - a)]
  · calc
      _ ≤ ‖(r : ℂ) * u‖ + ‖a‖ := norm_sub_le _ _
      _ = r + 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hu, ha, mul_one]
      _ ≤ 2 := by linarith only [hr1]

theorem abs_log_norm_radial_sub_le {u a : ℂ} (hu : ‖u‖ = 1) (ha : ‖a‖ = 1)
    (hne : u ≠ a) {r : ℝ} (hr : (1 / 2 : ℝ) ≤ r) (hr1 : r ≤ 1) :
    |Real.log ‖(r : ℂ) * u - a‖| ≤ Real.log 2 + |Real.log ‖u - a‖| := by
  have hd : 0 < ‖u - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨hlower, hupper⟩ := radial_circle_distance_bounds hu ha hr hr1
  have hrad : 0 < ‖(r : ℂ) * u - a‖ := (div_pos hd (by norm_num)).trans_le hlower
  have hloglower := Real.log_le_log (div_pos hd (by norm_num : (0 : ℝ) < 2)) hlower
  rw [Real.log_div hd.ne' (by norm_num)] at hloglower
  have hlogupper := Real.log_le_log hrad hupper
  apply abs_le.mpr
  constructor
  · linarith only [hloglower, neg_le_abs (Real.log ‖u - a‖)]
  · linarith only [hlogupper, abs_nonneg (Real.log ‖u - a‖)]

theorem ae_fourier_one_ne_on_unitInterval (a : ℂ) :
    ∀ᵐ t : ℝ ∂volume.restrict (Ioc (0 : ℝ) 1),
      fourier 1 (t : AddCircle (1 : ℝ)) ≠ a := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hsub : {t : ℝ | t ∈ Ioc (0 : ℝ) 1 ∧
      fourier 1 (t : AddCircle (1 : ℝ)) = a}.Subsingleton := by
    intro x hx y hy
    have hfourier := hx.2.trans hy.2.symm
    have hcircle : AddCircle.toCircle (x : AddCircle (1 : ℝ)) =
        AddCircle.toCircle (y : AddCircle (1 : ℝ)) := by
      apply Subtype.ext
      simpa only [fourier_one] using hfourier
    have hquot := AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0) hcircle
    have hx' : x ∈ Ioc (0 : ℝ) (0 + 1) := by simpa only [zero_add] using hx.1
    have hy' : y ∈ Ioc (0 : ℝ) (0 + 1) := by simpa only [zero_add] using hy.1
    have he : (⟨x, hx'⟩ : Ioc (0 : ℝ) (0 + 1)) = ⟨y, hy'⟩ := by
      apply (AddCircle.equivIoc (1 : ℝ) 0).symm.injective
      exact hquot
    exact congrArg Subtype.val he
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hsub.countable.ae_not_mem (volume : Measure ℝ)] with t ht
  intro htI htval
  exact ht ⟨htI, htval⟩

end DirichletL

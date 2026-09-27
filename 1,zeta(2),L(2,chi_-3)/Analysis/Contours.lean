import Mathlib

/-!
Certified contour estimates used as the analytic interface for later
holonomy arguments. The actual CDT-specific conformal maps and boundary
estimates remain separate obligations.
-/

namespace DirichletL

open Complex Metric

/-- Cauchy's derivative bound on a disk, via Mathlib's circle-integral API.

The function is complex differentiable on the open disk and continuous on its
closure through `DiffContOnCl`; the boundary estimate is required on the
circle of radius `R`. -/
theorem contour_derivative_bound {c : ℂ} {R C : ℝ} {f : ℂ → ℂ} (hR : 0 < R)
    (hd : DiffContOnCl ℂ f (ball c R))
    (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖deriv f c‖ ≤ C / R := by
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hd hC

/-- The rational lune map in CDT Appendix equation `firstgobble`. -/
noncomputable def luneMap (c z : ℂ) : ℂ :=
  z * ((c ^ 2 + 1) + (c ^ 2 - 1) * z) /
    ((c ^ 2 - 1) + (c ^ 2 + 1) * z)

/-- Cross-multiplication gives the quadratic relation behind the source's
square-root inverse formula. -/
theorem luneMap_quadratic {c z : ℂ}
    (hden : (c ^ 2 - 1) + (c ^ 2 + 1) * z ≠ 0) :
    (c ^ 2 - 1) * z ^ 2 + (c ^ 2 + 1) * z * (1 - luneMap c z) -
        (c ^ 2 - 1) * luneMap c z = 0 := by
  have he : luneMap c z * ((c ^ 2 - 1) + (c ^ 2 + 1) * z) =
      z * ((c ^ 2 + 1) + (c ^ 2 - 1) * z) := div_mul_cancel₀ _ hden
  linear_combination -he

/-- The lune denominator is nonzero on the source's inner disk radius. -/
theorem luneMap_denominator_ne_zero_of_norm_lt {c : ℝ} {z : ℂ} (hc : 1 < c)
    (hz : ‖z‖ < (c ^ 2 - 1) / (c ^ 2 + 1)) :
    ((c : ℂ) ^ 2 - 1) + ((c : ℂ) ^ 2 + 1) * z ≠ 0 := by
  intro hden
  have hcplus : c ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg c]
  have hcastplus : ((c : ℂ) ^ 2 + 1) ≠ 0 := by
    exact_mod_cast hcplus
  have hz_eq : z = -((c ^ 2 - 1) / (c ^ 2 + 1) : ℝ) := by
    have hrewrite :
        -((c ^ 2 - 1) / (c ^ 2 + 1) : ℝ) =
          -(((c : ℂ) ^ 2 - 1) / ((c : ℂ) ^ 2 + 1)) := by
      norm_num [ofReal_pow]
    rw [hrewrite, ← neg_div]
    apply (eq_div_iff hcastplus).2
    norm_num [ofReal_pow] at hden ⊢
    linear_combination hden
  rw [hz_eq] at hz
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_div] at hz
  have hpos : 0 < c ^ 2 - 1 := by
    nlinarith
  have hplus : 0 < c ^ 2 + 1 := by
    nlinarith [sq_nonneg c]
  rw [abs_of_pos hpos, abs_of_pos hplus] at hz
  exact (not_lt_of_ge (le_refl _)) hz

/-- The explicit lune map is holomorphic on the corresponding inner disk. -/
theorem differentiableOn_luneMap_ofReal_innerDisk {c : ℝ} (hc : 1 < c) :
    DifferentiableOn ℂ (luneMap (c : ℂ))
      (Metric.ball (0 : ℂ) ((c ^ 2 - 1) / (c ^ 2 + 1))) := by
  intro z hz
  have hz' : ‖z‖ < (c ^ 2 - 1) / (c ^ 2 + 1) := by
    simpa [mem_ball, dist_zero_right] using hz
  have hden := luneMap_denominator_ne_zero_of_norm_lt hc hz'
  have hnum : DifferentiableAt ℂ
      (fun w : ℂ => w * ((c : ℂ) ^ 2 + 1 + ((c : ℂ) ^ 2 - 1) * w)) z := by
    fun_prop
  have hdenfun : DifferentiableAt ℂ
      (fun w : ℂ => ((c : ℂ) ^ 2 - 1) + ((c : ℂ) ^ 2 + 1) * w) z := by
    fun_prop
  exact (hnum.div hdenfun hden).differentiableWithinAt

/-- The explicit lune map has unit norm on the unit-circle boundary. -/
theorem norm_luneMap_ofReal_of_norm_eq_one {c : ℝ} {z : ℂ} (hc : 1 < c)
    (hz : ‖z‖ = 1) : ‖luneMap (c : ℂ) z‖ = 1 := by
  have hcplus : c ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg c]
  have hcastplus : ((c : ℂ) ^ 2 + 1) ≠ 0 := by
    exact_mod_cast hcplus
  have hden : ((c : ℂ) ^ 2 - 1) + ((c : ℂ) ^ 2 + 1) * z ≠ 0 := by
    intro hden
    have hz_eq : z = -((c ^ 2 - 1) / (c ^ 2 + 1) : ℝ) := by
      have hrewrite :
          -((c ^ 2 - 1) / (c ^ 2 + 1) : ℝ) =
            -(((c : ℂ) ^ 2 - 1) / ((c : ℂ) ^ 2 + 1)) := by
        norm_num [ofReal_pow]
      rw [hrewrite, ← neg_div]
      apply (eq_div_iff hcastplus).2
      norm_num [ofReal_pow] at hden ⊢
      linear_combination hden
    rw [hz_eq, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_div] at hz
    have hpos : 0 < c ^ 2 - 1 := by nlinarith
    have hplus : 0 < c ^ 2 + 1 := by nlinarith [sq_nonneg c]
    rw [abs_of_pos hpos, abs_of_pos hplus] at hz
    have hEq : c ^ 2 - 1 = 1 * (c ^ 2 + 1) :=
      (div_eq_iff (ne_of_gt hplus)).mp hz
    nlinarith
  have hnorm :
      ‖((c : ℂ) ^ 2 + 1) + ((c : ℂ) ^ 2 - 1) * z‖ =
        ‖((c : ℂ) ^ 2 - 1) + ((c : ℂ) ^ 2 + 1) * z‖ := by
    have hzsq : Complex.normSq z = 1 := by
      rw [← Complex.sq_norm, hz]
      norm_num
    have hsq :
        ‖((c : ℂ) ^ 2 + 1) + ((c : ℂ) ^ 2 - 1) * z‖ ^ 2 =
          ‖((c : ℂ) ^ 2 - 1) + ((c : ℂ) ^ 2 + 1) * z‖ ^ 2 := by
      have hA : (c : ℂ) ^ 2 + 1 = ((c ^ 2 + 1 : ℝ) : ℂ) := by
        norm_num [ofReal_pow]
      have hB : (c : ℂ) ^ 2 - 1 = ((c ^ 2 - 1 : ℝ) : ℂ) := by
        norm_num [ofReal_pow]
      rw [hA, hB]
      rw [Complex.sq_norm, Complex.sq_norm]
      rw [Complex.normSq_add, Complex.normSq_add]
      simp only [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_one]
      norm_num [Complex.normSq_apply, ofReal_pow] at hzsq ⊢
      ring_nf at hzsq ⊢
      nlinarith
    nlinarith [norm_nonneg (((c : ℂ) ^ 2 + 1) + ((c : ℂ) ^ 2 - 1) * z),
      norm_nonneg (((c : ℂ) ^ 2 - 1) + ((c : ℂ) ^ 2 + 1) * z)]
  unfold luneMap
  rw [norm_div, norm_mul, hz, hnorm]
  simp only [one_mul]
  exact (div_self (norm_ne_zero_iff.mpr hden))

/-- The lune map sends the negative unit endpoint to the positive unit endpoint. -/
theorem luneMap_neg_one (c : ℂ) : luneMap c (-1) = 1 := by
  unfold luneMap
  have hden : (c ^ 2 - 1) + (c ^ 2 + 1) * (-1) = -2 := by
    ring
  rw [hden]
  ring

/-- The other unit endpoint has the same image when `c` is nonzero. -/
theorem luneMap_one {c : ℂ} (hc : c ≠ 0) : luneMap c 1 = 1 := by
  unfold luneMap
  field_simp [show c ^ 2 ≠ 0 from pow_ne_zero 2 hc]
  ring

/-- The inner real intersection point of the lune boundary maps to `-1`. -/
theorem luneMap_innerPoint {c : ℂ} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (hcp : c + 1 ≠ 0) :
    luneMap c (-(c - 1) / (c + 1)) = -1 := by
  have hden_eq :
      (c ^ 2 - 1) + (c ^ 2 + 1) * (-(c - 1) / (c + 1)) =
        2 * c * (c - 1) / (c + 1) := by
    field_simp [hcp]
    ring
  have hden : (c ^ 2 - 1) + (c ^ 2 + 1) * (-(c - 1) / (c + 1)) ≠ 0 := by
    rw [hden_eq]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hc0)
      (sub_ne_zero.mpr hc1)) hcp
  change (-(c - 1) / (c + 1)) *
      ((c ^ 2 + 1) + (c ^ 2 - 1) * (-(c - 1) / (c + 1))) /
        ((c ^ 2 - 1) + (c ^ 2 + 1) * (-(c - 1) / (c + 1))) = -1
  apply (div_eq_iff hden).2
  rw [hden_eq]
  field_simp [hcp]
  ring

/-- The inner-point normalization specializes to the source's real parameter. -/
theorem luneMap_innerPoint_ofReal {c : ℝ} (hc : 1 < c) :
    luneMap (c : ℂ) (-((c - 1) / (c + 1) : ℝ) : ℂ) = -1 := by
  have hc0 : (c : ℂ) ≠ 0 := by
    exact_mod_cast (by nlinarith : c ≠ 0)
  have hc1 : (c : ℂ) ≠ 1 := by
    exact_mod_cast (by nlinarith : c ≠ 1)
  have hcp : (c : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (by nlinarith : c + 1 ≠ 0)
  have h := luneMap_innerPoint hc0 hc1 hcp
  convert h using 1
  push_cast
  ring

/-- The lune map is holomorphic at the origin when its denominator is nonzero. -/
theorem hasDerivAt_luneMap_zero {c : ℂ} (hc : c ^ 2 - 1 ≠ 0) :
    HasDerivAt (luneMap c) ((c ^ 2 + 1) / (c ^ 2 - 1)) 0 := by
  have hnum : HasDerivAt
      (fun z : ℂ => z * ((c ^ 2 + 1) + (c ^ 2 - 1) * z))
      (c ^ 2 + 1) 0 := by
    convert (hasDerivAt_id (𝕜 := ℂ) 0).mul
      ((hasDerivAt_const (𝕜 := ℂ) 0 (c ^ 2 + 1)).add
        ((hasDerivAt_const (𝕜 := ℂ) 0 (c ^ 2 - 1)).mul
          (hasDerivAt_id (𝕜 := ℂ) 0))) using 1
    simp
  have hden : HasDerivAt
      (fun z : ℂ => (c ^ 2 - 1) + (c ^ 2 + 1) * z)
      (c ^ 2 + 1) 0 := by
    convert (hasDerivAt_const (𝕜 := ℂ) 0 (c ^ 2 - 1)).add
      ((hasDerivAt_const (𝕜 := ℂ) 0 (c ^ 2 + 1)).mul
        (hasDerivAt_id (𝕜 := ℂ) 0)) using 1
    simp
  have hc0 : c ^ 2 - 1 + (c ^ 2 + 1) * 0 ≠ 0 := by simpa using hc
  convert hnum.div hden hc0 using 1
  simp [luneMap]
  field_simp

/-- The source's real lune parameter `c > 1` satisfies the local denominator
condition for the explicit map. -/
theorem hasDerivAt_luneMap_ofReal_zero {c : ℝ} (hc : 1 < c) :
    HasDerivAt (luneMap (c : ℂ))
      (((c : ℂ) ^ 2 + 1) / ((c : ℂ) ^ 2 - 1)) 0 := by
  apply hasDerivAt_luneMap_zero
  have hreal : c ^ 2 - 1 ≠ 0 := by nlinarith
  exact_mod_cast hreal

/- The source uses the derivative norm at the origin as the local distortion
   factor.  This equality keeps that factor in exact real arithmetic. -/
theorem norm_deriv_luneMap_ofReal_zero {c : ℝ} (hc : 1 < c) :
    ‖deriv (luneMap (c : ℂ)) 0‖ = (c ^ 2 + 1) / (c ^ 2 - 1) := by
  rw [(hasDerivAt_luneMap_ofReal_zero hc).deriv]
  have hrewrite :
      (((c : ℂ) ^ 2 + 1) / ((c : ℂ) ^ 2 - 1)) =
        (((c ^ 2 + 1 : ℝ) : ℂ) / ((c ^ 2 - 1 : ℝ) : ℂ)) := by
    norm_num [ofReal_pow]
  rw [hrewrite, norm_div, Complex.norm_real, Complex.norm_real]
  rw [Real.norm_eq_abs]
  have hpos : 0 < c ^ 2 - 1 := by nlinarith
  rw [abs_of_pos (by nlinarith [sq_nonneg c] : 0 < c ^ 2 + 1)]
  rw [Real.norm_eq_abs, abs_of_pos hpos]

/-- The exact conformal-radius product for CDT's Appendix contour choice.

This records equation `exactconformal` for the rational parameters
`R = 77/100`, `c = 75/10`, and the four slit parameters in the source. -/
noncomputable def cdtContourConformalRadius : ℝ :=
  (995 / 1000 : ℝ) * (77 / 100) *
    (((75 / 10 : ℝ) ^ 2 - 1) / ((75 / 10 : ℝ) ^ 2 + 1)) *
    (4 * (91 / 100 : ℝ) / (1 + 91 / 100) ^ 2) *
    (4 * (6188 / 10000 : ℝ) / (1 + 6188 / 10000) ^ 2) *
    (4 * (55515 / 100000 : ℝ) / (1 + 55515 / 100000) ^ 2) *
    (4 * (772 / 1000 : ℝ) / (1 + 772 / 1000) ^ 2)

/-- Exact rational value of the selected contour's conformal-radius product. -/
theorem cdtContourConformalRadius_eq :
    cdtContourConformalRadius =
      (5448339453535586608000000000 /
        8658833407565631122430056127 : ℝ) := by
  norm_num [cdtContourConformalRadius]

/-- The selected contour radius is strictly larger than one half. -/
theorem cdtContourConformalRadius_gt_half :
    (1 / 2 : ℝ) < cdtContourConformalRadius := by
  rw [cdtContourConformalRadius_eq]
  norm_num

end DirichletL

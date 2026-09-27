import Analysis.FunctionsHRealIdentity
import Analysis.FunctionsHRemainder
import Analysis.ZagierRealSingularity

/-!
The actual special-value coefficient limits and overconvergence bounds
in CDT v2, Section 11.1, Lemma `defabc` (3). The independent boundary
-/

namespace DirichletL

open Filter Set
open scoped Topology ENNReal

private theorem coefficient_limit_eq_of_hauptmodul {p : PowerSeries ℚ} {f : ℂ → ℂ}
    {g : ℝ → ℝ} (ℓ L : ℝ) (hf : HasFPowerSeriesOnBall f (complexSeries p) 0 (1 / 9))
    (hr : (1 : ℝ≥0∞) ≤ (complexSeries p - (ℓ : ℂ) • complexSeries zagierGenerating).radius)
    (hid : ∀ q : ℝ, 0 < q → q < 1 → f (hauptmodulProduct (q : ℂ)) =
      zagierAnalytic (hauptmodulProduct (q : ℂ)) * (g q : ℂ))
    (hg : Tendsto g (𝓝[<] (1 : ℝ)) (𝓝 L)) : ℓ = L := by
  let x : ℝ → ℝ := fun q => (hauptmodulProduct (q : ℂ)).re
  let s := complexSeries p - (ℓ : ℂ) • complexSeries zagierGenerating
  have hpos : ∀ᶠ q : ℝ in 𝓝[<] 1, 0 < q :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ q : ℝ in 𝓝[<] 1, q < 1 := self_mem_nhdsWithin
  have hx (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
      x q ∈ Ioo (0 : ℝ) (1 / 9) ∧ (x q : ℂ) = hauptmodulProduct (q : ℂ) := by
    obtain ⟨r, hr, he⟩ := hauptmodulProduct_ofReal_mem hq0 hq1
    have hxr : x q = r := by simp only [x, ← he, Complex.ofReal_re]
    exact ⟨by rwa [hxr], by rwa [hxr]⟩
  have hxl : Tendsto x (𝓝[<] (1 : ℝ)) (𝓝[<] (1 / 9 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa [x] using
        Complex.continuous_re.continuousAt.tendsto.comp
          tendsto_hauptmodulProduct_ofReal_nhdsLT_one
    · filter_upwards [hpos, hlt] with q hq0 hq1
      exact (hx q hq0 hq1).1.2
  have hs : HasFPowerSeriesOnBall s.sum s 0 1 :=
    (s.hasFPowerSeriesOnBall (zero_lt_one.trans_le hr)).mono zero_lt_one hr
  have hsc : ContinuousAt s.sum (1 / 9 : ℂ) :=
    (hs.analyticAt_of_mem (by
      rw [← ENNReal.ofReal_one, Metric.emetric_ball]
      norm_num)).continuousAt
  have hn : Tendsto (fun q : ℝ => (s.sum (hauptmodulProduct (q : ℂ))).re)
      (𝓝[<] (1 : ℝ)) (𝓝 (s.sum (1 / 9 : ℂ)).re) :=
    (Complex.continuous_re.continuousAt.comp hsc).tendsto.comp
      tendsto_hauptmodulProduct_ofReal_nhdsLT_one
  have ha := tendsto_zagierReal_nhdsLT.comp hxl
  have hs_eq {z : ℂ} (hz : z ∈ EMetric.ball 0 (1 / 9 : ℝ≥0∞)) :
      s.sum z = f z - (ℓ : ℂ) * zagierAnalytic z := by
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zero_add] using
      ((hf.sub (hasFPowerSeriesOnBall_zagierAnalytic.const_smul (c := (ℓ : ℂ)))).sum hz).symm
  have hzero : Tendsto (fun q => g q - ℓ) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    apply (hn.div_atTop ha).congr'
    filter_upwards [hpos, hlt] with q hq0 hq1
    obtain ⟨hxq, hxcast⟩ := hx q hq0 hq1
    have hz : hauptmodulProduct (q : ℂ) ∈ EMetric.ball 0 (1 / 9 : ℝ≥0∞) := by
      rw [← hxcast, show (1 / 9 : ℝ≥0∞) = ENNReal.ofReal (1 / 9 : ℝ) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
          ENNReal.ofReal_ofNat],
        Metric.emetric_ball]
      simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hxq.1] using hxq.2
    have hare : (zagierAnalytic (hauptmodulProduct (q : ℂ))).re = zagierReal (x q) := by
      rw [← hxcast]
      rfl
    have hapos : 0 < zagierReal (x q) :=
      zero_lt_one.trans_le (one_le_zagierReal hxq.1.le hxq.2)
    rw [hs_eq hz, hid q hq0 hq1]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero, hare]
    apply (div_eq_iff hapos.ne').mpr
    ring
  have he : L - ℓ = 0 := tendsto_nhds_unique (hg.sub_const ℓ) hzero
  linarith

/-- The actual B coefficient limit, its polynomial error, and radius at least one. -/
theorem hB_coefficient_limit :
    Tendsto (fun n => (PowerSeries.coeff (R := ℚ) n hB : ℝ) / (zagierC n : ℝ)) atTop
      (𝓝 (lTwoChiMinusThree / 2)) ∧
    (∀ n, |(lTwoChiMinusThree / 2) * (zagierC n : ℝ) - (PowerSeries.coeff (R := ℚ) n hB : ℝ)| ≤
      8 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2) ∧
    (1 : ℝ≥0∞) ≤ (complexSeries hB -
      ((lTwoChiMinusThree / 2 : ℝ) : ℂ) • complexSeries zagierGenerating).radius := by
  obtain ⟨ℓ, hℓ, hbound, hr⟩ := exists_hB_coefficient_limit
  have he : ℓ = lTwoChiMinusThree / 2 := coefficient_limit_eq_of_hauptmodul
    ℓ (lTwoChiMinusThree / 2) hasFPowerSeriesOnBall_hBAnalytic hr
    (fun q hq0 hq1 => by
      rw [hBAnalytic_hauptmodulProduct hq0.le hq1, betaAnalytic_ofReal hq0.le hq1])
    (by simpa only [nhdsWithin_Ico_eq_nhdsLT (by norm_num : (0 : ℝ) < 1)] using
      tendsto_tsum_betaCoeff_mul_pow)
  subst ℓ
  exact ⟨hℓ, hbound, hr⟩

/-- The actual C coefficient limit, its polynomial error, and radius at least one. -/
theorem hC_coefficient_limit :
    Tendsto (fun n => (PowerSeries.coeff (R := ℚ) n hC : ℝ) / (zagierC n : ℝ)) atTop
      (𝓝 (zetaTwo / 4)) ∧
    (∀ n, |(zetaTwo / 4) * (zagierC n : ℝ) - (PowerSeries.coeff (R := ℚ) n hC : ℝ)| ≤
      8 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2) ∧
    (1 : ℝ≥0∞) ≤ (complexSeries hC -
      ((zetaTwo / 4 : ℝ) : ℂ) • complexSeries zagierGenerating).radius := by
  obtain ⟨ℓ, hℓ, hbound, hr⟩ := exists_hC_coefficient_limit
  have he : ℓ = zetaTwo / 4 := coefficient_limit_eq_of_hauptmodul
    ℓ (zetaTwo / 4) hasFPowerSeriesOnBall_hCAnalytic hr
    (fun q hq0 hq1 => by
      rw [hCAnalytic_hauptmodulProduct hq0.le hq1, gammaAnalytic_ofReal hq0.le hq1])
    (by simpa only [nhdsWithin_Ico_eq_nhdsLT (by norm_num : (0 : ℝ) < 1)] using
      tendsto_tsum_gammaCoeff_mul_pow)
  subst ℓ
  exact ⟨hℓ, hbound, hr⟩

/-- CDT equation `defH`: a relation among the special values gives radius at least one. -/
theorem one_le_radius_h_linearCombination (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0) :
    (1 : ℝ≥0∞) ≤ (complexSeries (a • hA + b • hB + c • hC)).radius := by
  let sB := complexSeries hB - ((lTwoChiMinusThree / 2 : ℝ) : ℂ) •
    complexSeries zagierGenerating
  let sC := complexSeries hC - ((zetaTwo / 4 : ℝ) : ℂ) • complexSeries zagierGenerating
  have hrelC : (a : ℂ) + (b : ℂ) * ((lTwoChiMinusThree / 2 : ℝ) : ℂ) +
      (c : ℂ) * ((zetaTwo / 4 : ℝ) : ℂ) = 0 := by exact_mod_cast hrel
  have he : complexSeries (a • hA + b • hB + c • hC) = (b : ℂ) • sB + (c : ℂ) • sC := by
    funext n
    apply ContinuousMultilinearMap.ext
    intro v
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      FormalMultilinearSeries.apply_eq_prod_smul_coeff]
    congr 1
    simp only [sB, sC, FormalMultilinearSeries.coeff, FormalMultilinearSeries.add_apply,
      FormalMultilinearSeries.sub_apply, FormalMultilinearSeries.smul_apply,
      ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.sub_apply,
      ContinuousMultilinearMap.smul_apply, complexSeries,
      Pi.one_def, FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one,
      map_add, map_smul, Rat.cast_add, Rat.cast_mul, hA]
    linear_combination (PowerSeries.coeff (R := ℚ) n zagierGenerating : ℂ) * hrelC
  rw [he]
  exact (le_min (hB_coefficient_limit.2.2.trans FormalMultilinearSeries.radius_le_smul)
    (hC_coefficient_limit.2.2.trans FormalMultilinearSeries.radius_le_smul)).trans
      (((b : ℂ) • sB).min_radius_le_radius_add ((c : ℂ) • sC))

end DirichletL

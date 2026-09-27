import Analysis.ZagierModularIdentity

/-!
Transfer the case-C modular identity to the exact q-series numerator.
Source: Zagier (2009), Section 5, equation (7), with the Hauptmodul from
CDT v2 Section 11.1, equation `haupt`.
The inverse of `qParam` is Mathlib's `Function.Periodic.invQParam`; this file
checks the upper-half-plane condition, clears the nonzero product factors, and
then applies analytic power-series uniqueness at the origin.
-/

namespace DirichletL

open Complex Filter Function.Periodic
open _root_.UpperHalfPlane hiding I
open scoped Topology Manifold MatrixGroups ModularForm CongruenceSubgroup Real

theorem invQParam_one_im_pos {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    0 < (invQParam 1 q).im := by
  have hnorm : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hlog : Real.log ‖q‖ < 0 := Real.log_neg hnorm hq
  rw [im_invQParam]
  norm_num
  have hpos : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
  have hcoef : (-1 / (2 * Real.pi) : ℝ) < 0 := by
    simpa only [neg_div] using (neg_lt_zero.mpr hpos)
  exact mul_pos_of_neg_of_neg hcoef hlog

theorem hauptmodulDerivativeClearedNumeratorAnalytic_eq_zero_of_norm
    {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1 / 2 ^ 25) :
    hauptmodulDerivativeClearedNumeratorAnalytic q = 0 := by
  have hq1 : ‖q‖ < 1 := hq.trans (by norm_num)
  let τ : ℍ := ⟨invQParam 1 q, invQParam_one_im_pos hq0 hq1⟩
  have hqparam : qParam 1 (τ : ℂ) = q := by
    change qParam 1 (invQParam 1 q) = q
    exact qParam_right_inv (by norm_num) hq0
  have hsmall : ‖qParam 1 (τ : ℂ)‖ < 1 / 2 ^ 25 := by
    simpa [hqparam] using hq
  have hform : zagierDerivativeDifferenceForm τ = 0 := by
    exact congrArg (fun f : ModularForm (CongruenceSubgroup.Gamma0 6) 2 => f τ)
      zagierDerivativeDifferenceForm_eq_zero
  have hprod : zagierDerivativeDifferenceProduct q = 0 := by
    have h := zagierDerivativeDifferenceForm_eq_product (τ := τ) hsmall
    rw [hqparam] at h
    rw [← h, hform]
  have hq6 : ‖q ^ 6‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq1 (by norm_num)
  have hHne : hauptmodulProduct q ≠ 0 := by
    have hEta : hauptmodulEta (τ : ℂ) = hauptmodulProduct q := by
      rw [hauptmodulEta_eq_product, hqparam]
    rw [← hEta]
    exact hauptmodulEta_ne_zero τ.im_pos
  have hHr : q * dslope hauptmodulProduct 0 q = hauptmodulProduct q := by
    have h := sub_smul_dslope hauptmodulProduct 0 q
    have hH0 : hauptmodulProduct 0 = 0 := by simp [hauptmodulProduct]
    simpa only [sub_zero, hH0, smul_eq_mul, zero_sub, add_zero] using h
  have hrne : dslope hauptmodulProduct 0 q ≠ 0 := by
    intro hr
    apply hHne
    rw [← hHr, hr, mul_zero]
  have hTne : qEulerProduct q ^ 6 * qEulerProduct (q ^ 6) ^ 4 ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 6 (qEulerProduct_ne_zero hq1))
      (pow_ne_zero 4 (qEulerProduct_ne_zero hq6))
  have hden : dslope hauptmodulProduct 0 q *
      (qEulerProduct q ^ 6 * qEulerProduct (q ^ 6) ^ 4) ≠ 0 :=
    mul_ne_zero hrne hTne
  have hcases : hauptmodulDerivativeClearedNumeratorAnalytic q = 0 ∨
      dslope hauptmodulProduct 0 q *
        (qEulerProduct q ^ 6 * qEulerProduct (q ^ 6) ^ 4) = 0 := by
    exact (div_eq_zero_iff.mp (by simpa [zagierDerivativeDifferenceProduct] using hprod))
  exact hcases.resolve_right hden

theorem hauptmodulDerivativeClearedNumeratorAnalytic_zero :
    hauptmodulDerivativeClearedNumeratorAnalytic 0 = 0 := by
  have h := hasFPowerSeriesAt_hauptmodulDerivativeClearedNumeratorRat.coeff_zero
    (fun _ => 1)
  have hc := coeff_zero_hauptmodulDerivativeClearedNumeratorRat 0 (by norm_num)
  have hc' : ((PowerSeries.coeff (R := ℚ) 0
      hauptmodulDerivativeClearedNumeratorRat : ℚ) : ℂ) = 0 := by
    simpa only [coeff_complexSeries] using hc
  have hcc' : PowerSeries.coeff (R := ℚ) 0 hauptmodulDerivativeClearedNumeratorRat = 0 := by
    exact_mod_cast hc'
  have hcc : PowerSeries.constantCoeff (R := ℚ) hauptmodulDerivativeClearedNumeratorRat = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hcc'
  simpa [complexSeries, FormalMultilinearSeries.ofScalars, hcc] using h.symm

theorem hauptmodulDerivativeClearedNumeratorAnalytic_eventually_eq_zero :
    hauptmodulDerivativeClearedNumeratorAnalytic =ᶠ[𝓝 (0 : ℂ)] (fun _ => 0) := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ)
    (by norm_num : (0 : ℝ) < 1 / 2 ^ 25)] with q hq
  have hq' : ‖q‖ < 1 / 2 ^ 25 := by
    simpa [Metric.mem_ball, dist_zero_right] using hq
  by_cases hq0 : q = 0
  · simpa [hq0] using hauptmodulDerivativeClearedNumeratorAnalytic_zero
  · exact hauptmodulDerivativeClearedNumeratorAnalytic_eq_zero_of_norm hq0 hq'

theorem hauptmodulDerivativeClearedNumeratorRat_eq_zero :
    hauptmodulDerivativeClearedNumeratorRat = 0 := by
  have hp := hasFPowerSeriesAt_hauptmodulDerivativeClearedNumeratorRat.eq_zero_of_eventually
    hauptmodulDerivativeClearedNumeratorAnalytic_eventually_eq_zero
  apply PowerSeries.ext
  intro n
  have hn := congrArg (fun s => s.coeff n) hp
  have hnc : ((PowerSeries.coeff (R := ℚ) n
      hauptmodulDerivativeClearedNumeratorRat : ℚ) : ℂ) = 0 := by
    dsimp at hn
    rw [coeff_complexSeries] at hn
    simpa only [FormalMultilinearSeries.zero_apply] using hn
  exact_mod_cast hnc

end DirichletL

import Analysis.HauptmodulAnalytic
import Analysis.FunctionalIndependence
import Analysis.PowerSeriesReversionAnalytic
import Analysis.QSeriesAnalytic
import Analysis.ZagierAnalytic

/-!
Local analytic realizations of the exact formal H_B and H_C in CDT v2,
Section 11.1, Lemma `defabc` (supplied `L2chi.tex` lines 7690-7742).
The forced equations are proved in `FunctionsHAnalyticODE.lean`.
Global continuation and overconvergence remain separate obligations.
-/

namespace DirichletL

open Filter
open scoped Topology ENNReal

theorem pos_radius_complexSeries_hauptmodulInverse :
    0 < (complexSeries (PowerSeries.map (Int.castRingHom ℚ) hauptmodulInverse)).radius := by
  rw [hauptmodulInverse, map_reversion]
  apply pos_radius_complexSeries_reversion
    (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1 / 2 ^ 25)
      le_radius_complexSeries_hauptmodul)
  · change (PowerSeries.constantCoeff (R := ℤ) hauptmodul : ℚ) = 0
    simp [constantCoeff_hauptmodul]
  · simp [coeff_one_hauptmodul]

/-- The complex sum of the existing integer inverse Hauptmodul series. -/
noncomputable def hauptmodulInverseAnalytic : ℂ → ℂ :=
  (complexSeries (PowerSeries.map (Int.castRingHom ℚ) hauptmodulInverse)).sum

theorem hasFPowerSeriesAt_hauptmodulInverseAnalytic :
    HasFPowerSeriesAt hauptmodulInverseAnalytic
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) hauptmodulInverse)) 0 :=
  (FormalMultilinearSeries.hasFPowerSeriesOnBall _
    pos_radius_complexSeries_hauptmodulInverse).hasFPowerSeriesAt

theorem hauptmodulInverseAnalytic_zero : hauptmodulInverseAnalytic 0 = 0 := by
  have h := hasFPowerSeriesAt_hauptmodulInverseAnalytic.coeff_zero (fun _ => 1)
  simpa [complexSeries, FormalMultilinearSeries.ofScalars,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_hauptmodulInverse] using h.symm

theorem deriv_hauptmodulInverseAnalytic_zero : deriv hauptmodulInverseAnalytic 0 = 1 := by
  have h := hasFPowerSeriesAt_hauptmodulInverseAnalytic.deriv
  simpa [complexSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    coeff_one_hauptmodulInverse] using h

theorem hauptmodulInverseAnalytic_left_inverse :
    (hauptmodulInverseAnalytic ∘ hauptmodulAnalytic) =ᶠ[𝓝 0] id := by
  have h0 : PowerSeries.constantCoeff (R := ℚ)
      (PowerSeries.map (Int.castRingHom ℚ) hauptmodul) = 0 := by
    change (PowerSeries.constantCoeff (R := ℤ) hauptmodul : ℚ) = 0
    simp [constantCoeff_hauptmodul]
  have h := hasFPowerSeriesAt_powerSeries_subst hasFPowerSeriesAt_hauptmodulInverseAnalytic
    hasFPowerSeriesAt_hauptmodulAnalytic h0
  rw [hauptmodulInverse, map_reversion,
    subst_reversion _ h0
      (by simp [coeff_one_hauptmodul])] at h
  filter_upwards [h.eventually_hasSum_sub, hasFPowerSeriesAt_complexSeries_X.eventually_hasSum_sub]
    with z hz h'z
  exact hz.unique h'z

theorem hauptmodulInverseAnalytic_right_inverse :
    (hauptmodulAnalytic ∘ hauptmodulInverseAnalytic) =ᶠ[𝓝 0] id := by
  have h0 : PowerSeries.constantCoeff (R := ℚ)
      (PowerSeries.map (Int.castRingHom ℚ) hauptmodul) = 0 := by
    change (PowerSeries.constantCoeff (R := ℤ) hauptmodul : ℚ) = 0
    simp [constantCoeff_hauptmodul]
  have h := hasFPowerSeriesAt_powerSeries_subst hasFPowerSeriesAt_hauptmodulAnalytic
    hasFPowerSeriesAt_hauptmodulInverseAnalytic (by
      change (PowerSeries.constantCoeff (R := ℤ) hauptmodulInverse : ℚ) = 0
      simp [constantCoeff_hauptmodulInverse])
  rw [hauptmodulInverse, map_reversion,
    reversion_subst _ h0
      (by simp [coeff_one_hauptmodul])] at h
  filter_upwards [h.eventually_hasSum_sub, hasFPowerSeriesAt_complexSeries_X.eventually_hasSum_sub]
    with z hz h'z
  exact hz.unique h'z

theorem exists_analyticAt_hauptmodul_localInverse :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧
      (g ∘ hauptmodulAnalytic) =ᶠ[𝓝 0] id ∧
      (hauptmodulAnalytic ∘ g) =ᶠ[𝓝 0] id := by
  exact ⟨hauptmodulInverseAnalytic, hasFPowerSeriesAt_hauptmodulInverseAnalytic.analyticAt,
    hauptmodulInverseAnalytic_zero, hauptmodulInverseAnalytic_left_inverse,
    hauptmodulInverseAnalytic_right_inverse⟩

theorem hasFPowerSeriesAt_hB_product :
    HasFPowerSeriesAt
      (fun z => zagierAnalytic z * betaAnalytic (hauptmodulInverseAnalytic z))
      (complexSeries hB) 0 := by
  simpa only [hB, Function.comp_apply] using
    hasFPowerSeriesAt_powerSeries_mul hasFPowerSeriesOnBall_zagierAnalytic.hasFPowerSeriesAt
      (hasFPowerSeriesAt_powerSeries_subst hasFPowerSeriesAt_betaAnalytic
        hasFPowerSeriesAt_hauptmodulInverseAnalytic (by
          change (PowerSeries.constantCoeff (R := ℤ) hauptmodulInverse : ℚ) = 0
          simp [constantCoeff_hauptmodulInverse]))

theorem hasFPowerSeriesAt_hC_product :
    HasFPowerSeriesAt
      (fun z => zagierAnalytic z * gammaAnalytic (hauptmodulInverseAnalytic z))
      (complexSeries hC) 0 := by
  simpa only [hC, Function.comp_apply] using
    hasFPowerSeriesAt_powerSeries_mul hasFPowerSeriesOnBall_zagierAnalytic.hasFPowerSeriesAt
      (hasFPowerSeriesAt_powerSeries_subst hasFPowerSeriesAt_gammaAnalytic
        hasFPowerSeriesAt_hauptmodulInverseAnalytic (by
          change (PowerSeries.constantCoeff (R := ℤ) hauptmodulInverse : ℚ) = 0
          simp [constantCoeff_hauptmodulInverse]))

theorem pos_radius_complexSeries_hB : 0 < (complexSeries hB).radius :=
  hasFPowerSeriesAt_hB_product.radius_pos

theorem pos_radius_complexSeries_hC : 0 < (complexSeries hC).radius :=
  hasFPowerSeriesAt_hC_product.radius_pos

/-- The complex sum of the original formal H_B series. -/
noncomputable def hBAnalytic : ℂ → ℂ := (complexSeries hB).sum

/-- The complex sum of the original formal H_C series. -/
noncomputable def hCAnalytic : ℂ → ℂ := (complexSeries hC).sum

theorem hasFPowerSeriesAt_hBAnalytic :
    HasFPowerSeriesAt hBAnalytic (complexSeries hB) 0 :=
  ((complexSeries hB).hasFPowerSeriesOnBall pos_radius_complexSeries_hB).hasFPowerSeriesAt

theorem hasFPowerSeriesAt_hCAnalytic :
    HasFPowerSeriesAt hCAnalytic (complexSeries hC) 0 :=
  ((complexSeries hC).hasFPowerSeriesOnBall pos_radius_complexSeries_hC).hasFPowerSeriesAt

theorem hBAnalytic_eq_product :
    hBAnalytic =ᶠ[𝓝 0]
      (fun z => zagierAnalytic z * betaAnalytic (hauptmodulInverseAnalytic z)) := by
  filter_upwards [hasFPowerSeriesAt_hBAnalytic.eventually_hasSum_sub,
    hasFPowerSeriesAt_hB_product.eventually_hasSum_sub] with z hz h'z
  exact hz.unique h'z

theorem hCAnalytic_eq_product :
    hCAnalytic =ᶠ[𝓝 0]
      (fun z => zagierAnalytic z * gammaAnalytic (hauptmodulInverseAnalytic z)) := by
  filter_upwards [hasFPowerSeriesAt_hCAnalytic.eventually_hasSum_sub,
    hasFPowerSeriesAt_hC_product.eventually_hasSum_sub] with z hz h'z
  exact hz.unique h'z

theorem hBAnalytic_zero : hBAnalytic 0 = 0 := by
  have h := hasFPowerSeriesAt_hBAnalytic.coeff_zero (fun _ => 1)
  simpa [complexSeries, FormalMultilinearSeries.ofScalars,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hB_constantCoeff] using h.symm

theorem hCAnalytic_zero : hCAnalytic 0 = 0 := by
  have h := hasFPowerSeriesAt_hCAnalytic.coeff_zero (fun _ => 1)
  simpa [complexSeries, FormalMultilinearSeries.ofScalars,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hC_constantCoeff] using h.symm

theorem deriv_hBAnalytic_zero : deriv hBAnalytic 0 = 1 := by
  have h := hasFPowerSeriesAt_hBAnalytic.deriv
  simpa [complexSeries, FormalMultilinearSeries.ofScalars_apply_eq, hB_coeff_one] using h

theorem deriv_hCAnalytic_zero : deriv hCAnalytic 0 = 1 := by
  have h := hasFPowerSeriesAt_hCAnalytic.deriv
  simpa [complexSeries, FormalMultilinearSeries.ofScalars_apply_eq, hC_coeff_one] using h

theorem analyticAt_hBAnalytic : AnalyticAt ℂ hBAnalytic 0 :=
  hasFPowerSeriesAt_hBAnalytic.analyticAt

theorem analyticAt_hCAnalytic : AnalyticAt ℂ hCAnalytic 0 :=
  hasFPowerSeriesAt_hCAnalytic.analyticAt

end DirichletL

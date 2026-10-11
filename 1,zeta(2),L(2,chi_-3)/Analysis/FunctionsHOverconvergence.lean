import Analysis.FunctionsHSpecialValues
import Analysis.FunctionsHContinuation

/-!
The actual combined H-series on the unit disk under CDT v2's normalized
rational relation, and its continuation with the forcing in equation `defH`.
This uses Lemma `defabc` (3) and Proposition `functionsH`, and supplies an
actual initial germ for the continuation argument in Lemma `14functions`.
-/

namespace DirichletL

open Filter
open scoped Topology NNReal ENNReal

/-- The actual sum of the combined rational H-series. -/
noncomputable def hLinearCombinationAnalytic (a b c : ℚ) : ℂ → ℂ :=
  (complexSeries (a • hA + b • hB + c • hC)).sum

theorem hasFPowerSeriesOnBall_hLinearCombinationAnalytic (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0) :
    HasFPowerSeriesOnBall (hLinearCombinationAnalytic a b c)
      (complexSeries (a • hA + b • hB + c • hC)) 0 1 := by
  have hr := one_le_radius_h_linearCombination a b c hrel
  exact ((complexSeries (a • hA + b • hB + c • hC)).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le hr)).mono zero_lt_one hr

theorem analyticAt_hLinearCombinationAnalytic (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    {z : ℂ} (hz : ‖z‖ < 1) : AnalyticAt ℂ (hLinearCombinationAnalytic a b c) z := by
  apply (hasFPowerSeriesOnBall_hLinearCombinationAnalytic a b c hrel).analyticAt_of_mem
  rw [← ENNReal.ofReal_one, Metric.emetric_ball]
  simpa only [Metric.mem_ball, dist_zero_right] using hz

theorem hLinearCombinationAnalytic_eq (a b c : ℚ) {z : ℂ} (hz : ‖z‖ < 1 / 9) :
    hLinearCombinationAnalytic a b c z =
      (a : ℂ) * zagierAnalytic z + (b : ℂ) * hBAnalytic z + (c : ℂ) * hCAnalytic z := by
  have hm : z ∈ EMetric.ball 0 (1 / 9 : ℝ≥0∞) := by
    apply mem_emetric_ball_zero_iff.mpr
    have hz' : ‖z‖₊ < (1 / 9 : ℝ≥0) := by exact_mod_cast hz
    simpa using ENNReal.coe_lt_coe.mpr hz'
  have hsum : HasSum
      (fun n => (PowerSeries.coeff (R := ℚ) n (a • hA + b • hB + c • hC) : ℂ) * z ^ n)
      ((a : ℂ) * zagierAnalytic z + (b : ℂ) * hBAnalytic z + (c : ℂ) * hCAnalytic z) := by
    have hsA := hasSum_of_hasFPowerSeriesOnBall hasFPowerSeriesOnBall_zagierAnalytic hm
    have hsB := hasSum_of_hasFPowerSeriesOnBall hasFPowerSeriesOnBall_hBAnalytic hm
    have hsC := hasSum_of_hasFPowerSeriesOnBall hasFPowerSeriesOnBall_hCAnalytic hm
    convert ((hsA.mul_left (a : ℂ)).add (hsB.mul_left (b : ℂ))).add
      (hsC.mul_left (c : ℂ)) using 1
    ext n
    simp only [hA, map_add, map_smul, Rat.cast_add, smul_eq_mul, Rat.cast_mul,
      add_mul, mul_assoc]
  change FormalMultilinearSeries.ofScalarsSum
    (fun n => (PowerSeries.coeff (R := ℚ) n (a • hA + b • hB + c • hC) : ℂ)) z = _
  simpa only [FormalMultilinearSeries.ofScalars_sum_eq, smul_eq_mul] using hsum.tsum_eq

theorem hLinearCombinationAnalytic_ode (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    {z : ℂ} (hz : ‖z‖ < 1) :
    zagierSecondOrderODE (hLinearCombinationAnalytic a b c) z =
      (b : ℂ) + (c : ℂ) / (1 - z) := by
  have hm : z ∈ EMetric.ball 0 (1 : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_one, Metric.emetric_ball]
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hs := hasSum_generatingODE (hasFPowerSeriesOnBall_hLinearCombinationAnalytic a b c hrel) hm
  rw [generatingODE_h_linearCombination] at hs
  have hforcing : HasSum
      (fun n => (PowerSeries.coeff (R := ℚ) n
        (generatingSeries (fun k => if k = 0 then b + c else c)) : ℂ) * z ^ n)
      ((b : ℂ) + (c : ℂ) / (1 - z)) := by
    convert (hasSum_ite_eq (0 : ℕ) (b : ℂ)).add
      ((hasSum_geometric_of_norm_lt_one hz).mul_left (c : ℂ)) using 1
    ext n
    by_cases hn : n = 0 <;> simp [generatingSeries, hn]
  exact hs.unique hforcing

/-- The actual overconvergent combination continues along every original regular path. -/
theorem exists_analyticContinuationAlong_hLinearCombination (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (γ : C(unitInterval, hForcedRegularSet)) (hγ : ‖(γ 0 : ℂ)‖ < 1) :
    ∃ F : unitInterval → ℂ → ℂ,
      AnalyticContinuationAlong (fun t => (γ t : ℂ)) F ∧
      F 0 =ᶠ[𝓝 (γ 0 : ℂ)] hLinearCombinationAnalytic a b c ∧
      ∀ t, ∀ᶠ z in 𝓝 (γ t : ℂ), zagierSecondOrderODE (F t) z =
        (b : ℂ) + (c : ℂ) / (1 - z) := by
  apply exists_analyticContinuationAlong_forcedH γ (hLinearCombinationAnalytic a b c) b c
    (analyticAt_hLinearCombinationAnalytic a b c hrel hγ)
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hγ] with z hz
  exact hLinearCombinationAnalytic_ode a b c hrel hz

end DirichletL

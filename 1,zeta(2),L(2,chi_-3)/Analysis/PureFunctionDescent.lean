import Analysis.PureFunctionPullback
import Analysis.PowerSeriesEvaluation
import Analysis.MobiusDescentAnalytic
import Analysis.MobiusAnalyticInvolution

/-!
The analytic B2, B3, and B4 of CDT v2, `defB` and Lemma `seven`
(supplied TeX lines 7327-7348 and 7915-7958). Factorial sums use norm
strictly below four; the pullback and branch identities are analytic germs at zero.
-/

namespace DirichletL

open Filter
open scoped Topology NNReal ENNReal

local notation "x" => (PowerSeries.X : PowerSeries ℚ)
local notation "A" => pureLogarithmSeries
local notation "L" => pureDilogarithmSeries

/-- The canonical analytic sum of the literal B2 factorial series. -/
noncomputable def pureB2 : ℂ → ℂ := (complexSeries pureB2Series).sum

/-- The canonical analytic sum of the literal B3 factorial series. -/
noncomputable def pureB3 : ℂ → ℂ := (complexSeries pureB3Series).sum

/-- The canonical analytic sum of the minus-symmetrized dilogarithm series. -/
noncomputable def pureB4 : ℂ → ℂ := (complexSeries pureB4Series).sum

theorem hasFPowerSeriesOnBall_pureB2 :
    HasFPowerSeriesOnBall pureB2 (complexSeries pureB2Series) 0 4 :=
  ((complexSeries pureB2Series).hasFPowerSeriesOnBall
    (lt_of_lt_of_le (by norm_num) le_radius_complexSeries_pureB2Series)).mono
    (by norm_num) le_radius_complexSeries_pureB2Series

theorem hasFPowerSeriesOnBall_pureB3 :
    HasFPowerSeriesOnBall pureB3 (complexSeries pureB3Series) 0 4 :=
  ((complexSeries pureB3Series).hasFPowerSeriesOnBall
    (lt_of_lt_of_le (by norm_num) le_radius_complexSeries_pureB3Series)).mono
    (by norm_num) le_radius_complexSeries_pureB3Series

private theorem mem_radius_four_ball {z : ℂ} (hz : ‖z‖ < 4) :
    z ∈ EMetric.ball 0 (4 : ℝ≥0∞) := by
  simpa only [EMetric.mem_ball, edist_zero_right, ← ofReal_norm_eq_enorm,
    ← ENNReal.ofReal_ofNat, ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 4)] using hz

theorem analyticAt_pureB2 {z : ℂ} (hz : ‖z‖ < 4) : AnalyticAt ℂ pureB2 z :=
  hasFPowerSeriesOnBall_pureB2.analyticAt_of_mem (mem_radius_four_ball hz)

theorem analyticAt_pureB3 {z : ℂ} (hz : ‖z‖ < 4) : AnalyticAt ℂ pureB3 z :=
  hasFPowerSeriesOnBall_pureB3.analyticAt_of_mem (mem_radius_four_ball hz)

/-- The literal source sum, with its first nonzero degree n+2. -/
theorem hasSum_pureB2 {z : ℂ} (hz : ‖z‖ < 4) :
    HasSum (fun n : ℕ =>
      ((2 * (n.factorial : ℚ) * (n + 2).factorial / (2 * n + 4).factorial : ℚ) : ℂ) *
        z ^ (n + 2)) (pureB2 z) := by
  have h := (hasSum_nat_add_iff' 2).mpr
    (hasSum_of_hasFPowerSeriesOnBall hasFPowerSeriesOnBall_pureB2 (mem_radius_four_ball hz))
  simpa only [coeff_pureB2Series_add_two, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_pureB2Series, coeff_one_pureB2Series, Rat.cast_zero,
    zero_mul, add_zero, sub_zero] using h

/-- The literal B3 sum, with index n+1 corresponding to the source's positive index. -/
theorem hasSum_pureB3 {z : ℂ} (hz : ‖z‖ < 4) :
    HasSum (fun n : ℕ =>
      (((n.factorial : ℚ) ^ 2 / (2 * n + 2).factorial : ℚ) : ℂ) * z ^ (n + 1))
      (pureB3 z) := by
  have h := (hasSum_nat_add_iff' 1).mpr
    (hasSum_of_hasFPowerSeriesOnBall hasFPowerSeriesOnBall_pureB3 (mem_radius_four_ball hz))
  simpa only [coeff_pureB3Series_succ, pureB3QuotientCoeff, Finset.sum_range_one,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_pureB3Series,
    Rat.cast_zero, zero_mul, sub_zero] using h

@[simp]
theorem pureB2_zero : pureB2 0 = 0 := by
  change FormalMultilinearSeries.ofScalarsSum
    (fun n => (PowerSeries.coeff (R := ℚ) n pureB2Series : ℂ)) 0 = 0
  simp [FormalMultilinearSeries.ofScalarsSum_zero]

@[simp]
theorem deriv_pureB2_zero : deriv pureB2 0 = 0 := by
  simpa [coeff_complexSeries] using hasFPowerSeriesOnBall_pureB2.hasFPowerSeriesAt.deriv

@[simp]
theorem pureB3_zero : pureB3 0 = 0 := by
  change FormalMultilinearSeries.ofScalarsSum
    (fun n => (PowerSeries.coeff (R := ℚ) n pureB3Series : ℂ)) 0 = 0
  simp [FormalMultilinearSeries.ofScalarsSum_zero]

@[simp]
theorem deriv_pureB3_zero : deriv pureB3 0 = 1 / 2 := by
  simpa [coeff_complexSeries] using hasFPowerSeriesOnBall_pureB3.hasFPowerSeriesAt.deriv

private theorem tendsto_involution_zero :
    Tendsto mobiusAnalyticInvolution (𝓝 (0 : ℂ)) (𝓝 0) := by
  simpa [mobiusAnalyticInvolution] using
    (analyticAt_mobiusAnalyticInvolution (by norm_num : (0 : ℂ) ≠ 1)).continuousAt.tendsto

private theorem tendsto_coordinate_zero : Tendsto mobiusCoordinate (𝓝 (0 : ℂ)) (𝓝 0) := by
  simpa [mobiusCoordinate] using
    (analyticAt_mobiusCoordinate (by norm_num : (0 : ℂ) ≠ 1)).continuousAt.tendsto

private theorem eventually_hasSum_X_mul {p : PowerSeries ℚ} {f : ℂ → ℂ}
    (h : ∀ᶠ z : ℂ in 𝓝 0,
      HasSum (fun n => (PowerSeries.coeff (R := ℚ) n p : ℂ) * z ^ n) (f z)) :
    ∀ᶠ z : ℂ in 𝓝 0,
      HasSum (fun n => (PowerSeries.coeff (R := ℚ) n (x * p) : ℂ) * z ^ n) (z * f z) := by
  filter_upwards [h] with z hz
  simpa only [Polynomial.coe_X, Polynomial.aeval_X] using hasSum_polynomial_mul hz Polynomial.X

private theorem trace_pullback_of_hasSum {p : PowerSeries ℚ} {f : ℂ → ℂ}
    (h : ∀ᶠ z : ℂ in 𝓝 0,
      HasSum (fun n => (PowerSeries.coeff (R := ℚ) n p : ℂ) * z ^ n) (f z)) :
    (fun z => symmetrizedAnalytic p (mobiusCoordinate z)) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => f z + f (mobiusAnalyticInvolution z)) := by
  have ht := symmetrizedAnalytic_pullback_of_pos_radius p
    (pos_radius_complexSeries_of_eventually_hasSum h)
  have he : (complexSeries p).sum =ᶠ[𝓝 (0 : ℂ)] f := by
    filter_upwards [h] with z hz
    exact sum_complexSeries_eq_of_hasSum hz
  filter_upwards [ht, he, he.comp_tendsto tendsto_involution_zero] with z hz hzx hzw
  simp only [Function.comp_apply] at hzw
  change symmetrizedAnalytic p (mobiusCoordinate z) =
    (complexSeries p).sum z + (complexSeries p).sum (mobiusAnalyticInvolution z) at hz
  rwa [hzx, hzw] at hz

theorem pureB3_eq_symmetrizedAnalytic : pureB3 = symmetrizedAnalytic L := by
  simp only [pureB3, symmetrizedAnalytic, symmetrizedDescent_pureDilogarithmSeries]

theorem neg_clog_one_sub_mobiusAnalyticInvolution :
    (fun z : ℂ => -Complex.log (1 - mobiusAnalyticInvolution z)) =ᶠ[𝓝 0]
      (fun z => Complex.log (1 - z)) := by
  have h := trace_pullback_of_hasSum
    (eventually_hasSum_of_hasFPowerSeriesAt hasFPowerSeriesOnBall_neg_clog_one_sub.hasFPowerSeriesAt)
  have hzero (z : ℂ) : symmetrizedAnalytic A z = 0 := by
    rw [symmetrizedAnalytic, symmetrizedDescent_pureLogarithmSeries]
    change FormalMultilinearSeries.ofScalarsSum
      (fun n => (PowerSeries.coeff (R := ℚ) n (0 : PowerSeries ℚ) : ℂ)) z = 0
    rw [FormalMultilinearSeries.ofScalars_sum_eq]
    simp
  filter_upwards [h] with z hz
  rw [hzero] at hz
  linear_combination -hz

private theorem hasSum_twice_X (z : ℂ) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n (2 * x) : ℂ) * z ^ n) (2 * z) := by
  rw [← map_ofNat (PowerSeries.C (R := ℚ)) 2]
  convert hasSum_ite_eq (1 : ℕ) (2 * z) using 1
  ext n
  by_cases hn : n = 1
  · subst n
    simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
  · simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X, hn, Ne.symm hn]

theorem pureB2_eq_symmetrizedAnalytic :
    pureB2 =ᶠ[𝓝 (0 : ℂ)] (fun z => 2 * z + symmetrizedAnalytic (x * A) z) := by
  have hx := eventually_hasSum_X_mul
    (eventually_hasSum_of_hasFPowerSeriesAt hasFPowerSeriesOnBall_neg_clog_one_sub.hasFPowerSeriesAt)
  have hr := pos_radius_complexSeries_symmetrizedDescent (x * A)
    (pos_radius_complexSeries_of_eventually_hasSum hx)
  have ht := eventually_hasSum_of_hasFPowerSeriesAt
    ((complexSeries (symmetrizedDescent (x * A))).hasFPowerSeriesOnBall hr).hasFPowerSeriesAt
  filter_upwards [ht] with z hz
  apply sum_complexSeries_eq_of_hasSum
  simpa only [pureB2Series_eq_symmetrizedDescent, map_add, Rat.cast_add, add_mul] using
    (hasSum_twice_X z).add hz

theorem pureB2_pullback :
    (fun z : ℂ => pureB2 (mobiusCoordinate z)) =ᶠ[𝓝 0]
      (fun z => 2 * mobiusCoordinate z +
        (z - mobiusAnalyticInvolution z) * (-Complex.log (1 - z))) := by
  have ht := trace_pullback_of_hasSum (eventually_hasSum_X_mul
    (eventually_hasSum_of_hasFPowerSeriesAt hasFPowerSeriesOnBall_neg_clog_one_sub.hasFPowerSeriesAt))
  filter_upwards [pureB2_eq_symmetrizedAnalytic.comp_tendsto tendsto_coordinate_zero,
    ht, neg_clog_one_sub_mobiusAnalyticInvolution] with z hb ht ha
  simp only [Function.comp_apply] at hb
  rw [ht, ha] at hb
  linear_combination hb

theorem pureB3_pullback :
    (fun z : ℂ => pureB3 (mobiusCoordinate z)) =ᶠ[𝓝 0]
      (fun z => pureDilogarithm z + pureDilogarithm (mobiusAnalyticInvolution z)) := by
  simpa only [pureB3_eq_symmetrizedAnalytic] using trace_pullback_of_hasSum
    (eventually_hasSum_of_hasFPowerSeriesAt hasFPowerSeriesOnBall_pureDilogarithm.hasFPowerSeriesAt)

private theorem eventually_hasSum_pureB4 :
    ∀ᶠ z : ℂ in 𝓝 0,
      HasSum (fun n => (PowerSeries.coeff (R := ℚ) n pureB4Series : ℂ) * z ^ n)
        (2 * symmetrizedAnalytic (x * L) z - z * pureB3 z) := by
  have hx := eventually_hasSum_X_mul
    (eventually_hasSum_of_hasFPowerSeriesAt hasFPowerSeriesOnBall_pureDilogarithm.hasFPowerSeriesAt)
  have hr := pos_radius_complexSeries_symmetrizedDescent (x * L)
    (pos_radius_complexSeries_of_eventually_hasSum hx)
  have ht := eventually_hasSum_of_hasFPowerSeriesAt
    ((complexSeries (symmetrizedDescent (x * L))).hasFPowerSeriesOnBall hr).hasFPowerSeriesAt
  filter_upwards [ht, eventually_hasSum_of_hasFPowerSeriesAt
    hasFPowerSeriesOnBall_pureB3.hasFPowerSeriesAt] with z ht hb
  have hs := (hasSum_polynomial_mul ht (Polynomial.C 2)).sub
    (hasSum_polynomial_mul hb Polynomial.X)
  simpa only [pureB4Series, map_sub, Rat.cast_sub, sub_mul, Polynomial.coe_C,
    Polynomial.coe_X, Polynomial.aeval_C, Polynomial.aeval_X, Rat.cast_ofNat] using hs

theorem pos_radius_complexSeries_pureB4Series : 0 < (complexSeries pureB4Series).radius :=
  pos_radius_complexSeries_of_eventually_hasSum eventually_hasSum_pureB4

theorem hasFPowerSeriesAt_pureB4 : HasFPowerSeriesAt pureB4 (complexSeries pureB4Series) 0 :=
  ((complexSeries pureB4Series).hasFPowerSeriesOnBall
    pos_radius_complexSeries_pureB4Series).hasFPowerSeriesAt

theorem analyticAt_pureB4 : AnalyticAt ℂ pureB4 0 := hasFPowerSeriesAt_pureB4.analyticAt

theorem pureB4_eq_symmetrizedAnalytic :
    pureB4 =ᶠ[𝓝 (0 : ℂ)] (fun z => 2 * symmetrizedAnalytic (x * L) z - z * pureB3 z) := by
  filter_upwards [eventually_hasSum_pureB4] with z hz
  exact sum_complexSeries_eq_of_hasSum hz

theorem pureB4_pullback :
    (fun z : ℂ => pureB4 (mobiusCoordinate z)) =ᶠ[𝓝 0]
      (fun z => (z - mobiusAnalyticInvolution z) *
        (pureDilogarithm z - pureDilogarithm (mobiusAnalyticInvolution z))) := by
  have ht := trace_pullback_of_hasSum (eventually_hasSum_X_mul
    (eventually_hasSum_of_hasFPowerSeriesAt hasFPowerSeriesOnBall_pureDilogarithm.hasFPowerSeriesAt))
  filter_upwards [pureB4_eq_symmetrizedAnalytic.comp_tendsto tendsto_coordinate_zero,
    ht, pureB3_pullback] with z hb ht h3
  simp only [Function.comp_apply] at hb
  rw [ht, h3] at hb
  dsimp only [mobiusCoordinate, mobiusAnalyticInvolution] at hb ⊢
  linear_combination hb

@[simp]
theorem pureB4_zero : pureB4 0 = 0 := by
  change FormalMultilinearSeries.ofScalarsSum
    (fun n => (PowerSeries.coeff (R := ℚ) n pureB4Series : ℂ)) 0 = 0
  simp [FormalMultilinearSeries.ofScalarsSum_zero]

@[simp]
theorem deriv_pureB4_zero : deriv pureB4 0 = -4 := by
  simpa [coeff_complexSeries] using hasFPowerSeriesAt_pureB4.deriv

theorem two_mul_pureB3_pullback :
    (fun z : ℂ => 2 * pureB3 (mobiusCoordinate z)) =ᶠ[𝓝 0]
      (fun z => -Complex.log (1 - z) ^ 2) := by
  have hlog := eventually_hasSum_of_hasFPowerSeriesAt
    hasFPowerSeriesOnBall_neg_clog_one_sub.hasFPowerSeriesAt
  have hsquare : ∀ᶠ z : ℂ in 𝓝 0,
      HasSum (fun n => (PowerSeries.coeff (R := ℚ) n (A ^ 2) : ℂ) * z ^ n)
        ((-Complex.log (1 - z)) ^ 2) := by
    filter_upwards [hlog] with z hz
    simpa only [pow_two] using hasSum_powerSeries_mul hz hz
  have ht := trace_pullback_of_hasSum hsquare
  have he : symmetrizedAnalytic (A ^ 2) =ᶠ[𝓝 (0 : ℂ)] (fun z => -4 * pureB3 z) := by
    filter_upwards [eventually_hasSum_of_hasFPowerSeriesAt
      hasFPowerSeriesOnBall_pureB3.hasFPowerSeriesAt] with z hz
    rw [symmetrizedAnalytic, symmetrizedDescent_sq_pureLogarithmSeries]
    apply sum_complexSeries_eq_of_hasSum
    simpa [PowerSeries.coeff_C_mul, mul_assoc] using hz.mul_left (-4 : ℂ)
  filter_upwards [he.comp_tendsto tendsto_coordinate_zero, ht,
    neg_clog_one_sub_mobiusAnalyticInvolution] with z he ht ha
  simp only [Function.comp_apply] at he
  rw [ha] at ht
  linear_combination (1 / 2 : ℂ) * he - (1 / 2 : ℂ) * ht

theorem pureDilogarithm_mobiusAnalyticInvolution :
    (fun z : ℂ => pureDilogarithm (mobiusAnalyticInvolution z)) =ᶠ[𝓝 0]
      (fun z => -pureDilogarithm z - Complex.log (1 - z) ^ 2 / 2) := by
  filter_upwards [two_mul_pureB3_pullback, pureB3_pullback] with z hs ht
  linear_combination (1 / 2 : ℂ) * hs - ht

end DirichletL

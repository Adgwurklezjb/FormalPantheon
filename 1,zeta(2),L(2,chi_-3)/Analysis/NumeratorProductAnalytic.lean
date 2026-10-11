import Analysis.NumeratorProductCoefficients
import Analysis.NumeratorSquareModularForms
import Analysis.ZagierSecondDerivativeAnalytic

/-!
Convergent realizations of the beta/gamma numerator-square differences.
Source: CDT v2, Section 11.1; Zagier (2009), Sections 5-6.
and the punctured order-seven limit used below.
-/

namespace DirichletL

open Filter
open scoped Topology

/-- The literal beta numerator in the complex q-coordinate. -/
noncomputable def betaNumeratorAnalytic (q : ℂ) : ℂ :=
  ∑' n : ℕ, (betaNumerator n : ℂ) * q ^ n

/-- The literal gamma numerator in the complex q-coordinate. -/
noncomputable def gammaNumeratorAnalytic (q : ℂ) : ℂ :=
  ∑' n : ℕ, (gammaNumerator n : ℂ) * q ^ n

theorem hasFPowerSeriesAt_betaNumeratorAnalytic :
    HasFPowerSeriesAt betaNumeratorAnalytic
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk betaNumerator)))
        0 := by
  apply hasFPowerSeriesAt_of_eventually_hasSum
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq
  have hq1 : ‖q‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hq
  simpa [betaNumeratorAnalytic] using (hasSum_betaNumerator_mul_pow_complex hq1).summable.hasSum

theorem hasFPowerSeriesAt_gammaNumeratorAnalytic :
    HasFPowerSeriesAt gammaNumeratorAnalytic
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk gammaNumerator)))
        0 := by
  apply hasFPowerSeriesAt_of_eventually_hasSum
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq
  have hq1 : ‖q‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hq
  simpa [gammaNumeratorAnalytic] using (hasSum_gammaNumerator_mul_pow_complex hq1).summable.hasSum

/-- The analytic beta square difference multiplied by the cube of the denominator. -/
noncomputable def betaNumeratorClearedAnalytic (q : ℂ) : ℂ :=
  betaNumeratorAnalytic q ^ 2 * zagierCaseCDAnalytic q ^ 3 -
    hauptmodulProduct q ^ 2 *
      (1 - 10 * hauptmodulProduct q + 9 * hauptmodulProduct q ^ 2) ^ 2 *
        zagierCaseCNAnalytic q ^ 3

/-- The corresponding analytic gamma square difference. -/
noncomputable def gammaNumeratorClearedAnalytic (q : ℂ) : ℂ :=
  gammaNumeratorAnalytic q ^ 2 * zagierCaseCDAnalytic q ^ 3 -
    hauptmodulProduct q ^ 2 * (1 - 9 * hauptmodulProduct q) ^ 2 *
      zagierCaseCNAnalytic q ^ 3

theorem hasFPowerSeriesAt_betaNumeratorClearedAnalytic :
    HasFPowerSeriesAt betaNumeratorClearedAnalytic
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) betaNumeratorClearedSeries)) 0 := by
  have hH := hasFPowerSeriesAt_hauptmodulProduct
  have h1 := hasFPowerSeriesAt_int_const 1
  have h9 := hasFPowerSeriesAt_int_const 9
  simp only [Int.cast_one, Int.cast_ofNat] at h1 h9
  have h10 := hasFPowerSeriesAt_int_const 10
  simp only [Int.cast_ofNat] at h10
  have hN := hasFPowerSeriesAt_int_pow hasFPowerSeriesAt_zagierCaseCNAnalytic 3
  have hD := hasFPowerSeriesAt_int_pow hasFPowerSeriesAt_zagierCaseCDAnalytic 3
  exact hasFPowerSeriesAt_int_sub
    (hasFPowerSeriesAt_int_mul
      (hasFPowerSeriesAt_int_pow hasFPowerSeriesAt_betaNumeratorAnalytic 2) hD)
    (hasFPowerSeriesAt_int_mul
      (hasFPowerSeriesAt_int_mul (hasFPowerSeriesAt_int_pow hH 2)
        (hasFPowerSeriesAt_int_pow
          (hasFPowerSeriesAt_int_add
            (hasFPowerSeriesAt_int_sub h1
              (hasFPowerSeriesAt_int_mul h10 hH))
            (hasFPowerSeriesAt_int_mul h9
              (hasFPowerSeriesAt_int_pow hH 2))) 2)) hN)

theorem hasFPowerSeriesAt_gammaNumeratorClearedAnalytic :
    HasFPowerSeriesAt gammaNumeratorClearedAnalytic
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) gammaNumeratorClearedSeries)) 0 := by
  have hH := hasFPowerSeriesAt_hauptmodulProduct
  have h1 := hasFPowerSeriesAt_int_const 1
  have h9 := hasFPowerSeriesAt_int_const 9
  simp only [Int.cast_one, Int.cast_ofNat] at h1 h9
  have hN := hasFPowerSeriesAt_int_pow hasFPowerSeriesAt_zagierCaseCNAnalytic 3
  have hD := hasFPowerSeriesAt_int_pow hasFPowerSeriesAt_zagierCaseCDAnalytic 3
  exact hasFPowerSeriesAt_int_sub
    (hasFPowerSeriesAt_int_mul
      (hasFPowerSeriesAt_int_pow hasFPowerSeriesAt_gammaNumeratorAnalytic 2) hD)
    (hasFPowerSeriesAt_int_mul
      (hasFPowerSeriesAt_int_mul (hasFPowerSeriesAt_int_pow hH 2)
        (hasFPowerSeriesAt_int_pow
          (hasFPowerSeriesAt_int_sub h1
            (hasFPowerSeriesAt_int_mul h9 hH)) 2)) hN)

theorem tendsto_div_seventh_betaNumeratorClearedAnalytic :
    Tendsto (fun q : ℂ => betaNumeratorClearedAnalytic q / q ^ 7) (𝓝[≠] 0)
      (𝓝 ((complexSeries (PowerSeries.map (Int.castRingHom ℚ)
        betaNumeratorClearedSeries)).coeff 7)) := by
  apply tendsto_div_pow_of_hasFPowerSeriesAt hasFPowerSeriesAt_betaNumeratorClearedAnalytic
  intro m hm
  simp [coeff_complexSeries, coeff_zero_betaNumeratorClearedSeries m hm]

theorem tendsto_div_seventh_gammaNumeratorClearedAnalytic :
    Tendsto (fun q : ℂ => gammaNumeratorClearedAnalytic q / q ^ 7) (𝓝[≠] 0)
      (𝓝 ((complexSeries (PowerSeries.map (Int.castRingHom ℚ)
        gammaNumeratorClearedSeries)).coeff 7)) := by
  apply tendsto_div_pow_of_hasFPowerSeriesAt hasFPowerSeriesAt_gammaNumeratorClearedAnalytic
  intro m hm
  simp [coeff_complexSeries, coeff_zero_gammaNumeratorClearedSeries m hm]

end DirichletL

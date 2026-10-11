import Analysis.ZagierClearedNumeratorAnalytic
import Analysis.ZagierSecondDerivativeCoefficients
import Analysis.IntegralPowerSeriesAnalytic

/-!
Convergent q-coordinate realization of the cleared second identity in
Zagier (2009), Section 5, equation (7), case C. The formal coefficients and
analytic exceptional points are recorded in
-/

namespace DirichletL

open Filter
open scoped Topology

/-- The analytic numerator of the case-C eta square in the q-coordinate. -/
noncomputable def zagierCaseCNAnalytic (q : ℂ) : ℂ :=
  qEulerProduct (q ^ 2) ^ 12 * qEulerProduct (q ^ 3) ^ 2

/-- The analytic denominator of the case-C eta square in the q-coordinate. -/
noncomputable def zagierCaseCDAnalytic (q : ℂ) : ℂ :=
  qEulerProduct q ^ 6 * qEulerProduct (q ^ 6) ^ 4

/-- Euler differentiation in the complex q-coordinate. -/
noncomputable def zagierThetaAnalytic (f : ℂ → ℂ) (q : ℂ) : ℂ := q * deriv f q

/-- The numerator of the first Euler derivative of N/D. -/
noncomputable def zagierClearAAnalytic (q : ℂ) : ℂ :=
  zagierThetaAnalytic zagierCaseCNAnalytic q * zagierCaseCDAnalytic q -
    zagierCaseCNAnalytic q * zagierThetaAnalytic zagierCaseCDAnalytic q

/-- The numerator of the second Euler derivative of N/D. -/
noncomputable def zagierClearBAnalytic (q : ℂ) : ℂ :=
  zagierThetaAnalytic zagierClearAAnalytic q * zagierCaseCDAnalytic q -
    2 * zagierClearAAnalytic q * zagierThetaAnalytic zagierCaseCDAnalytic q

/-- The polynomial factor on the right side of the second modular identity. -/
noncomputable def zagierClearPolynomialAnalytic (q : ℂ) : ℂ :=
  4 * hauptmodulProduct q *
      (1 - 10 * hauptmodulProduct q + 9 * hauptmodulProduct q ^ 2) *
      (9 * hauptmodulProduct q - 3)

/-- The analytic cleared difference for the second modular identity. -/
noncomputable def zagierSecondClearedAnalytic (q : ℂ) : ℂ :=
  3 * zagierClearAAnalytic q ^ 2 -
    2 * zagierCaseCNAnalytic q * zagierClearBAnalytic q -
    zagierClearPolynomialAnalytic q * zagierCaseCNAnalytic q ^ 4

private theorem hasFPowerSeriesAt_int_theta {p : PowerSeries ℤ} {f : ℂ → ℂ}
    (hf : HasFPowerSeriesAt f (complexSeries (PowerSeries.map (Int.castRingHom ℚ) p)) 0) :
    HasFPowerSeriesAt (zagierThetaAnalytic f)
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) (zagierTheta p))) 0 := by
  obtain ⟨r, hr⟩ := hf
  have hd := hasFPowerSeriesOnBall_derivativeFun hr
  have ht := hasFPowerSeriesAt_powerSeries_mul
    hasFPowerSeriesAt_complexSeries_X hd.hasFPowerSeriesAt
  have he : PowerSeries.map (Int.castRingHom ℚ) (zagierTheta p) =
      powerSeriesEuler ℚ (PowerSeries.map (Int.castRingHom ℚ) p) := by
    ext n
    simp [zagierTheta, PowerSeries.coeff_map, coeff_powerSeriesEuler]
  rw [he, powerSeriesEuler_apply]
  simpa only [zagierThetaAnalytic, id_eq] using ht

theorem hasFPowerSeriesAt_zagierCaseCNAnalytic :
    HasFPowerSeriesAt zagierCaseCNAnalytic
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) zagierCaseCN)) 0 := by
  simpa only [zagierCaseCN, zagierCaseCNAnalytic, caseCSquareNumeratorRat_eq_map] using
    hasFPowerSeriesAt_caseCSquareNumerator

theorem hasFPowerSeriesAt_zagierCaseCDAnalytic :
    HasFPowerSeriesAt zagierCaseCDAnalytic
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) zagierCaseCD)) 0 := by
  simpa only [zagierCaseCD, zagierCaseCDAnalytic, caseCSquareDenominatorRat_eq_map] using
    hasFPowerSeriesAt_caseCSquareDenominator

theorem hasFPowerSeriesAt_zagierClearAAnalytic :
    HasFPowerSeriesAt zagierClearAAnalytic
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) zagierClearA)) 0 := by
  exact hasFPowerSeriesAt_int_sub
    (hasFPowerSeriesAt_int_mul
      (hasFPowerSeriesAt_int_theta hasFPowerSeriesAt_zagierCaseCNAnalytic)
      hasFPowerSeriesAt_zagierCaseCDAnalytic)
    (hasFPowerSeriesAt_int_mul hasFPowerSeriesAt_zagierCaseCNAnalytic
      (hasFPowerSeriesAt_int_theta hasFPowerSeriesAt_zagierCaseCDAnalytic))

theorem hasFPowerSeriesAt_zagierClearBAnalytic :
    HasFPowerSeriesAt zagierClearBAnalytic
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) zagierClearB)) 0 := by
  exact hasFPowerSeriesAt_int_sub
    (hasFPowerSeriesAt_int_mul
      (hasFPowerSeriesAt_int_theta hasFPowerSeriesAt_zagierClearAAnalytic)
      hasFPowerSeriesAt_zagierCaseCDAnalytic)
    (hasFPowerSeriesAt_int_mul
      (hasFPowerSeriesAt_int_mul (hasFPowerSeriesAt_int_const 2)
        hasFPowerSeriesAt_zagierClearAAnalytic)
      (hasFPowerSeriesAt_int_theta hasFPowerSeriesAt_zagierCaseCDAnalytic))

theorem hasFPowerSeriesAt_zagierClearPolynomialAnalytic :
    HasFPowerSeriesAt zagierClearPolynomialAnalytic
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) zagierClearPolynomial)) 0 := by
  have h1 : HasFPowerSeriesAt (fun _ : ℂ => (1 : ℂ))
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) (1 : PowerSeries ℤ))) 0 := by
    simpa only [Int.cast_one] using hasFPowerSeriesAt_int_const 1
  have ht : HasFPowerSeriesAt hauptmodulProduct
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) zagierHauptmodul)) 0 :=
    hasFPowerSeriesAt_hauptmodulProduct
  exact hasFPowerSeriesAt_int_mul
    (hasFPowerSeriesAt_int_mul
      (hasFPowerSeriesAt_int_mul (hasFPowerSeriesAt_int_const 4) ht)
      (hasFPowerSeriesAt_int_add
        (hasFPowerSeriesAt_int_sub h1
          (hasFPowerSeriesAt_int_mul (hasFPowerSeriesAt_int_const 10) ht))
        (hasFPowerSeriesAt_int_mul (hasFPowerSeriesAt_int_const 9)
          (hasFPowerSeriesAt_int_pow ht 2))))
    (hasFPowerSeriesAt_int_sub
      (hasFPowerSeriesAt_int_mul (hasFPowerSeriesAt_int_const 9) ht)
      (hasFPowerSeriesAt_int_const 3))

theorem hasFPowerSeriesAt_zagierSecondClearedAnalytic :
    HasFPowerSeriesAt zagierSecondClearedAnalytic
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) zagierSecondClearedSeries)) 0 := by
  exact hasFPowerSeriesAt_int_sub
    (hasFPowerSeriesAt_int_sub
      (hasFPowerSeriesAt_int_mul (hasFPowerSeriesAt_int_const 3)
        (hasFPowerSeriesAt_int_pow hasFPowerSeriesAt_zagierClearAAnalytic 2))
      (hasFPowerSeriesAt_int_mul
        (hasFPowerSeriesAt_int_mul (hasFPowerSeriesAt_int_const 2)
          hasFPowerSeriesAt_zagierCaseCNAnalytic)
        hasFPowerSeriesAt_zagierClearBAnalytic))
    (hasFPowerSeriesAt_int_mul hasFPowerSeriesAt_zagierClearPolynomialAnalytic
      (hasFPowerSeriesAt_int_pow hasFPowerSeriesAt_zagierCaseCNAnalytic 4))

theorem coeff_zero_complexSeries_zagierSecondClearedSeries (m : ℕ) (hm : m < 5) :
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) zagierSecondClearedSeries)).coeff m =
      0 := by
  rw [coeff_complexSeries, PowerSeries.coeff_map, coeff_zero_zagierSecondClearedSeries m hm]
  simp

theorem tendsto_div_fifth_zagierSecondClearedAnalytic :
    Tendsto (fun q : ℂ => zagierSecondClearedAnalytic q / q ^ 5) (𝓝[≠] 0)
      (𝓝 ((complexSeries (PowerSeries.map (Int.castRingHom ℚ)
        zagierSecondClearedSeries)).coeff 5)) :=
  tendsto_div_pow_of_hasFPowerSeriesAt hasFPowerSeriesAt_zagierSecondClearedAnalytic
    coeff_zero_complexSeries_zagierSecondClearedSeries

end DirichletL

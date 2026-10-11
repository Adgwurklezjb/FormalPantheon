import Analysis.ZagierEtaSeries
import Analysis.ZagierSecondQSeriesIdentity
import Analysis.ZagierFormalQSeriesIdentity

/-!
The two case-C equations in the normalized integral eta series, following
Zagier (2009), Section 5, equation (7). The nonzero factors canceled below
-/

namespace DirichletL

private theorem euler_sq (f : PowerSeries ℤ) :
    powerSeriesEuler ℤ (f ^ 2) = 2 * f * powerSeriesEuler ℤ f := by
  simpa only [nsmul_eq_mul, smul_eq_mul, Nat.reduceSub, pow_one, Nat.cast_ofNat,
    mul_assoc] using
    (powerSeriesEuler ℤ).leibniz_pow f 2

theorem zagierClearA_eq_etaSeries :
    zagierClearA =
      2 * zagierEtaSeries * powerSeriesEuler ℤ zagierEtaSeries * zagierCaseCD ^ 2 := by
  simp only [zagierClearA, zagierTheta, zagierCaseCN_eq_etaSeries_sq_mul,
    Derivation.leibniz, euler_sq, smul_eq_mul]
  ring

theorem zagierClearB_eq_etaSeries :
    zagierClearB = 2 * ((powerSeriesEuler ℤ zagierEtaSeries) ^ 2 +
      zagierEtaSeries * powerSeriesEuler ℤ (powerSeriesEuler ℤ zagierEtaSeries)) *
        zagierCaseCD ^ 3 := by
  have h2 : powerSeriesEuler ℤ (2 : PowerSeries ℤ) = 0 :=
    (powerSeriesEuler ℤ).map_natCast 2
  simp only [zagierClearB, zagierTheta, zagierClearA_eq_etaSeries,
    Derivation.leibniz, euler_sq, h2, smul_eq_mul]
  ring

theorem powerSeriesEuler_hauptmodul_eq_etaSeries :
    powerSeriesEuler ℤ hauptmodul = hauptmodul * hauptmodulK * zagierEtaSeries ^ 2 := by
  apply mul_right_cancel₀ zagierCaseCD_ne_zero
  rw [powerSeriesEuler_hauptmodul]
  calc
    (hauptmodul * hauptmodulLogDerivativeSeries) * zagierCaseCD =
        hauptmodul * (hauptmodulLogDerivativeSeries * caseCSquareDenominator) := by
      rw [zagierCaseCD, mul_assoc]
    _ = hauptmodul * (hauptmodulK * zagierCaseCN) := by
      rw [hauptmodulLogDerivativeSeries_mul_caseCSquareDenominator_eq, zagierCaseCN]
    _ = (hauptmodul * hauptmodulK * zagierEtaSeries ^ 2) * zagierCaseCD := by
      rw [zagierCaseCN_eq_etaSeries_sq_mul]
      ring

theorem zagierEtaSeries_second_identity :
    2 * (powerSeriesEuler ℤ zagierEtaSeries) ^ 2 -
        zagierEtaSeries * powerSeriesEuler ℤ (powerSeriesEuler ℤ zagierEtaSeries) =
      hauptmodul * hauptmodulK * (9 * hauptmodul - 3) * zagierEtaSeries ^ 6 := by
  have h4 : (4 : PowerSeries ℤ) ≠ 0 := by
    intro h
    have hc := congrArg (PowerSeries.constantCoeff (R := ℤ)) h
    rw [← map_ofNat (PowerSeries.C (R := ℤ)), PowerSeries.constantCoeff_C] at hc
    norm_num at hc
  have hc : (4 : PowerSeries ℤ) * zagierEtaSeries ^ 2 * zagierCaseCD ^ 4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero h4 (pow_ne_zero 2 zagierEtaSeries_ne_zero))
      (pow_ne_zero 4 zagierCaseCD_ne_zero)
  apply mul_left_cancel₀ hc
  have h := zagier_second_formal_identity
  rw [zagierClearA_eq_etaSeries, zagierClearB_eq_etaSeries,
    zagierCaseCN_eq_etaSeries_sq_mul] at h
  simp only [zagierClearPolynomial, zagierHauptmodul, hauptmodulK, nsmul_eq_mul] at h ⊢
  convert h using 1 <;> ring

end DirichletL

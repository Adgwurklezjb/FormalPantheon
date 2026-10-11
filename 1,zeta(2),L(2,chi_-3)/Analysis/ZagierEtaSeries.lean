import Analysis.ZagierSecondDerivativeCoefficients

/-!
The normalized integral eta series in the case-C row of Zagier (2009),
Section 5, PDF page 8. Its square is the previously constructed eta square.
The source and unit checks are recorded in
-/

namespace DirichletL

/-- The numerator of the normalized case-C eta series. -/
noncomputable def zagierEtaNumerator : PowerSeries ℤ :=
  qEulerProductSeries 2 ^ 6 * qEulerProductSeries 3

/-- The denominator of the normalized case-C eta series. -/
noncomputable def zagierEtaDenominator : PowerSeries ℤ :=
  qEulerProductSeries 1 ^ 3 * qEulerProductSeries 6 ^ 2

/-- The integral eta series, with the inverse fixed by constant coefficient one. -/
noncomputable def zagierEtaSeries : PowerSeries ℤ :=
  zagierEtaNumerator * PowerSeries.invOfUnit zagierEtaDenominator (1 : ℤˣ)

theorem constantCoeff_zagierEtaNumerator :
    PowerSeries.constantCoeff (R := ℤ) zagierEtaNumerator = 1 := by
  simp [zagierEtaNumerator, constantCoeff_qEulerProductSeries (by norm_num : 0 < 2),
    constantCoeff_qEulerProductSeries (by norm_num : 0 < 3)]

theorem constantCoeff_zagierEtaDenominator :
    PowerSeries.constantCoeff (R := ℤ) zagierEtaDenominator = 1 := by
  simp [zagierEtaDenominator, constantCoeff_qEulerProductSeries (by norm_num : 0 < 1),
    constantCoeff_qEulerProductSeries (by norm_num : 0 < 6)]

theorem constantCoeff_zagierEtaSeries :
    PowerSeries.constantCoeff (R := ℤ) zagierEtaSeries = 1 := by
  simp [zagierEtaSeries, constantCoeff_zagierEtaNumerator]

theorem zagierEtaSeries_mul_denominator :
    zagierEtaSeries * zagierEtaDenominator = zagierEtaNumerator := by
  rw [zagierEtaSeries, mul_assoc,
    PowerSeries.invOfUnit_mul _ _ (by simpa using constantCoeff_zagierEtaDenominator),
    mul_one]

theorem zagierEtaNumerator_sq : zagierEtaNumerator ^ 2 = zagierCaseCN := by
  dsimp only [zagierEtaNumerator, zagierCaseCN, caseCSquareNumerator]
  ring

theorem zagierEtaDenominator_sq : zagierEtaDenominator ^ 2 = zagierCaseCD := by
  dsimp only [zagierEtaDenominator, zagierCaseCD, caseCSquareDenominator]
  ring

theorem zagierCaseCN_eq_etaSeries_sq_mul :
    zagierCaseCN = zagierEtaSeries ^ 2 * zagierCaseCD := by
  rw [← zagierEtaNumerator_sq, ← zagierEtaDenominator_sq,
    ← zagierEtaSeries_mul_denominator, mul_pow]

theorem zagierEtaSeries_ne_zero : zagierEtaSeries ≠ 0 := by
  intro h
  have hc := congrArg (PowerSeries.constantCoeff (R := ℤ)) h
  norm_num [constantCoeff_zagierEtaSeries] at hc

theorem zagierCaseCD_ne_zero : zagierCaseCD ≠ 0 := by
  intro h
  have hc := congrArg (PowerSeries.constantCoeff (R := ℤ)) h
  rw [← zagierEtaDenominator_sq, map_pow, constantCoeff_zagierEtaDenominator] at hc
  norm_num at hc

end DirichletL

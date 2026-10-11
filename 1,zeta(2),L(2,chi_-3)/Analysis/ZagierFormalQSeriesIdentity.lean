import Analysis.ZagierQSeriesTransfer
import Analysis.HauptmodulDifferential

/-!
The exact formal q-series identity obtained from Zagier (2009), Section 5,
equation (7), with CDT v2 Section 11.1's Hauptmodul normalization.
The analytic transfer proves that the cleared numerator vanishes; this file
rewrites that numerator with the formal Euler derivation and cancels the
-/

namespace DirichletL

theorem hauptmodulShift_eq_formalProduct :
    hauptmodulShift = formalProduct hauptFactor := by
  ext n
  simp [hauptmodulShift, hauptmodul, PowerSeries.coeff_succ_X_mul,
    coeff_formalProduct]

theorem hauptmodul_eq_X_mul_hauptmodulShift :
    hauptmodul = PowerSeries.X * hauptmodulShift := by
  rw [hauptmodulShift_eq_formalProduct]
  rfl

theorem powerSeriesEuler_hauptmodul_eq_X_mul_hauptmodulDerivativeNumerator :
    powerSeriesEuler ℤ hauptmodul = PowerSeries.X * hauptmodulDerivativeNumerator := by
  have hX : (PowerSeries.X : PowerSeries ℤ).derivativeFun = 1 :=
    PowerSeries.derivative_X
  rw [powerSeriesEuler_apply, hauptmodul, hauptmodulDerivativeNumerator,
    hauptmodulShift_eq_formalProduct, PowerSeries.derivativeFun_mul]
  rw [hX]
  simp only [smul_eq_mul, mul_one]
  ring

theorem hauptmodulDerivativeClearedNumerator_eq_zero :
    hauptmodulDerivativeClearedNumerator = 0 := by
  apply PowerSeries.ext
  intro n
  have h := congrArg (PowerSeries.coeff (R := ℚ) n)
    hauptmodulDerivativeClearedNumeratorRat_eq_zero
  have hc : ((PowerSeries.coeff (R := ℤ) n
      hauptmodulDerivativeClearedNumerator : ℤ) : ℚ) = 0 := by
    simpa [hauptmodulDerivativeClearedNumeratorRat, PowerSeries.coeff_map,
      Int.coe_castRingHom, Rat.cast_intCast] using h
  exact_mod_cast hc

theorem hauptmodul_ne_zero : hauptmodul ≠ 0 := by
  intro h
  have hc := congrArg (PowerSeries.coeff (R := ℤ) 1) h
  simp [coeff_one_hauptmodul] at hc

theorem hauptmodulLogDerivativeSeries_mul_caseCSquareDenominator_eq :
    hauptmodulLogDerivativeSeries * caseCSquareDenominator =
      hauptmodulK * caseCSquareNumerator := by
  have hprod : hauptmodul *
      (hauptmodulLogDerivativeSeries * caseCSquareDenominator -
        hauptmodulK * caseCSquareNumerator) = 0 := by
    have hnum' : powerSeriesEuler ℤ hauptmodul * caseCSquareDenominator -
        (hauptmodulK * caseCSquareNumerator) * hauptmodul = 0 := by
      rw [powerSeriesEuler_hauptmodul_eq_X_mul_hauptmodulDerivativeNumerator,
        hauptmodul_eq_X_mul_hauptmodulShift]
      calc
        PowerSeries.X * hauptmodulDerivativeNumerator * caseCSquareDenominator -
            (hauptmodulK * caseCSquareNumerator) *
              (PowerSeries.X * hauptmodulShift) =
            PowerSeries.X * (hauptmodulDerivativeNumerator * caseCSquareDenominator -
              (hauptmodulK * caseCSquareNumerator) * hauptmodulShift) := by ring
        _ = PowerSeries.X * hauptmodulDerivativeClearedNumerator := by
          rw [hauptmodulDerivativeClearedNumerator]
        _ = 0 := by rw [hauptmodulDerivativeClearedNumerator_eq_zero, mul_zero]
    calc
      hauptmodul *
          (hauptmodulLogDerivativeSeries * caseCSquareDenominator -
            hauptmodulK * caseCSquareNumerator) =
          (hauptmodul * hauptmodulLogDerivativeSeries) * caseCSquareDenominator -
            (hauptmodulK * caseCSquareNumerator) * hauptmodul := by ring
      _ = powerSeriesEuler ℤ hauptmodul * caseCSquareDenominator -
          (hauptmodulK * caseCSquareNumerator) * hauptmodul := by
        rw [powerSeriesEuler_hauptmodul]
      _ = 0 := hnum'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hauptmodul_ne_zero)

end DirichletL

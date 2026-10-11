import Arithmetic.PowerSeriesEuler

/-!
Second Euler derivatives of the literal beta/gamma q-series from CDT v2,
Section 11.1 (TeX lines 7646-7680). The numerator definitions retain the
-/

namespace DirichletL

theorem powerSeriesEuler_two_beta :
    powerSeriesEuler ℚ (powerSeriesEuler ℚ (PowerSeries.mk betaCoeff)) =
      PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk betaNumerator) :=
  powerSeriesEuler_two_mk_div_sq betaNumerator (by simp [betaNumerator])

theorem powerSeriesEuler_two_gamma :
    powerSeriesEuler ℚ (powerSeriesEuler ℚ (PowerSeries.mk gammaCoeff)) =
      PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk gammaNumerator) :=
  powerSeriesEuler_two_mk_div_sq gammaNumerator (by simp [gammaNumerator])

end DirichletL

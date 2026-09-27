import Analysis.HauptmodulBounds
import Analysis.PowerSeriesAnalytic

/-!
Local analytic realization of the exact formal Hauptmodul in CDT v2,
Section 11.1, equations `haupt` and `invert` (supplied `L2chi.tex`
lines 7619-7637). No modular uniformization is asserted here.
-/

namespace DirichletL

open Filter
open scoped Topology NNReal ENNReal

theorem le_radius_complexSeries_hauptmodul :
    (1 / 2 ^ 25 : ℝ≥0∞) ≤
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) hauptmodul)).radius := by
  suffices h : ((1 / 2 ^ 25 : ℝ≥0) : ℝ≥0∞) ≤
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) hauptmodul)).radius by
    simpa using h
  apply FormalMultilinearSeries.le_radius_of_bound _ 1
  intro n
  simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef, coeff_complexSeries,
    PowerSeries.coeff_map, Int.coe_castRingHom, Rat.cast_intCast,
    Complex.norm_intCast, NNReal.coe_div, NNReal.coe_one, NNReal.coe_pow, NNReal.coe_ofNat]
  calc
    |(PowerSeries.coeff (R := ℤ) n hauptmodul : ℝ)| * (1 / 2 ^ 25) ^ n ≤
        (2 ^ 25) ^ n * (1 / 2 ^ 25) ^ n := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast abs_coeff_hauptmodul_le n)
        (by positivity)
    _ = 1 := by rw [← mul_pow]; norm_num

/-- The complex sum of the existing integer Hauptmodul, cast through the rationals. -/
noncomputable def hauptmodulAnalytic : ℂ → ℂ :=
  (complexSeries (PowerSeries.map (Int.castRingHom ℚ) hauptmodul)).sum

theorem hasFPowerSeriesAt_hauptmodulAnalytic :
    HasFPowerSeriesAt hauptmodulAnalytic
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) hauptmodul)) 0 := by
  exact (FormalMultilinearSeries.hasFPowerSeriesOnBall _
    (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1 / 2 ^ 25)
      le_radius_complexSeries_hauptmodul)).hasFPowerSeriesAt

theorem hauptmodulAnalytic_zero : hauptmodulAnalytic 0 = 0 := by
  have h := hasFPowerSeriesAt_hauptmodulAnalytic.coeff_zero (fun _ => 1)
  simpa [complexSeries, FormalMultilinearSeries.ofScalars,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_hauptmodul] using h.symm

theorem deriv_hauptmodulAnalytic_zero : deriv hauptmodulAnalytic 0 = 1 := by
  have h := hasFPowerSeriesAt_hauptmodulAnalytic.deriv
  simpa [complexSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    coeff_one_hauptmodul] using h

end DirichletL

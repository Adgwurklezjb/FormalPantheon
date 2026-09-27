import Analysis.ZagierEtaSeriesDifferential
import Analysis.FunctionalIndependence
import Analysis.ZagierOperatorTransport

/-!
The case-C eta series equals the binomial generating series in the
Hauptmodul coordinate. This follows the calculation below equation (7) in
Zagier (2009), Section 5, and CDT v2 Lemma `defabc`. The preparation and
-/

namespace DirichletL

private theorem subst_generatingODE_eq_zero (f F H : PowerSeries ℚ)
    (hH0 : PowerSeries.constantCoeff (R := ℚ) H = 0) (hHne : H ≠ 0) (hfne : f ≠ 0)
    (hcomp : MvPowerSeries.subst (fun (_ : Unit) => H) F = f)
    (hH : powerSeriesEuler ℚ H = H * (1 - 10 * H + 9 * H ^ 2) * f ^ 2)
    (hf : 2 * (powerSeriesEuler ℚ f) ^ 2 -
        f * powerSeriesEuler ℚ (powerSeriesEuler ℚ f) =
      H * (1 - 10 * H + 9 * H ^ 2) * (9 * H - 3) * f ^ 6) :
    MvPowerSeries.subst (fun (_ : Unit) => H) (generatingODE F) = 0 := by
  have h := subst_generatingODE_mul_of_euler_identities f F H 1 hH0 hfne
    (by simpa only [mul_one] using hcomp) hH hf
  have he : H * (1 - 10 * H + 9 * H ^ 2) * f ^ 3 *
      MvPowerSeries.subst (fun (_ : Unit) => H) (generatingODE F) = 0 := by
    simpa using h
  have hKne : (1 - 10 * H + 9 * H ^ 2) ≠ 0 := by
    intro hz
    have h0 := congrArg (PowerSeries.constantCoeff (R := ℚ)) hz
    norm_num [hH0] at h0
  exact (mul_eq_zero.mp he).resolve_left
    (mul_ne_zero (mul_ne_zero hHne hKne) (pow_ne_zero 3 hfne))

/-- The case-C eta series is the binomial generating series in the Hauptmodul coordinate. -/
theorem zagierEtaSeries_eq_subst_zagierGenerating :
    PowerSeries.map (Int.castRingHom ℚ) zagierEtaSeries =
      MvPowerSeries.subst
        (fun (_ : Unit) => PowerSeries.map (Int.castRingHom ℚ) hauptmodul)
        zagierGenerating := by
  let f : PowerSeries ℚ := PowerSeries.map (Int.castRingHom ℚ) zagierEtaSeries
  let H : PowerSeries ℚ := PowerSeries.map (Int.castRingHom ℚ) hauptmodul
  let J : PowerSeries ℚ := reversion H
  let F : PowerSeries ℚ := MvPowerSeries.subst (fun (_ : Unit) => J) f
  have hH0 : PowerSeries.constantCoeff (R := ℚ) H = 0 := by
    dsimp only [H]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_hauptmodul, map_zero]
  have hH1 : PowerSeries.coeff (R := ℚ) 1 H = 1 := by
    simp only [H, PowerSeries.coeff_map, coeff_one_hauptmodul, map_one]
  have hf0 : PowerSeries.constantCoeff (R := ℚ) f = 1 := by
    dsimp only [f]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_zagierEtaSeries, map_one]
  have hHne : H ≠ 0 := by
    intro hz
    have hc := congrArg (PowerSeries.coeff (R := ℚ) 1) hz
    rw [hH1, map_zero] at hc
    exact one_ne_zero hc
  have hfne : f ≠ 0 := by
    intro hz
    have hc := congrArg (PowerSeries.constantCoeff (R := ℚ)) hz
    rw [hf0, map_zero] at hc
    exact one_ne_zero hc
  have hJ0 : PowerSeries.constantCoeff (R := ℚ) J = 0 := constantCoeff_reversion H
  have hsH : MvPowerSeries.HasSubst (fun (_ : Unit) => H) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hH0)
  have hsJ : MvPowerSeries.HasSubst (fun (_ : Unit) => J) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hJ0)
  have hcomp : MvPowerSeries.subst (fun (_ : Unit) => H) F = f := by
    dsimp only [F]
    rw [MvPowerSeries.subst_comp_subst_apply hsJ hsH, subst_reversion H hH0 hH1]
    convert congrFun (MvPowerSeries.subst_self (σ := Unit) (R := ℚ)) f using 1
  have hnormH := congrArg (PowerSeries.map (Int.castRingHom ℚ))
    powerSeriesEuler_hauptmodul_eq_etaSeries
  have hnormf := congrArg (PowerSeries.map (Int.castRingHom ℚ))
    zagierEtaSeries_second_identity
  simp only [hauptmodulK, nsmul_eq_mul, map_powerSeriesEuler, map_mul,
    map_sub, map_add, map_pow, map_ofNat, map_natCast, Nat.cast_ofNat, map_one] at hnormH hnormf
  have hode : generatingODE F = 0 := by
    apply subst_injective_of_coeff_one H hH0 hH1
    have hz := subst_generatingODE_eq_zero f F H hH0 hHne hfne hcomp hnormH hnormf
    simpa only [← MvPowerSeries.substAlgHom_apply hsH, map_zero] using hz
  have hF0 : PowerSeries.constantCoeff (R := ℚ) F = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    change PowerSeries.coeff (R := ℚ) 0 (MvPowerSeries.subst (fun (_ : Unit) => J) f) = 1
    rw [coeff_subst_zero hJ0, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0]
  have hF : F = zagierGenerating :=
    eq_zagierGenerating_of_generatingODE_eq_zero hode hF0
  change f = MvPowerSeries.subst (fun (_ : Unit) => H) zagierGenerating
  rw [← hF]
  exact hcomp.symm

end DirichletL

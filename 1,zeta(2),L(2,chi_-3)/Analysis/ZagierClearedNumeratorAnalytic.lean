import Analysis.AnalyticIntegrals
import Analysis.HauptmodulProductEvaluation
import Analysis.ModularVanishing
import Analysis.ZagierDerivativeCoefficients

/-!
Local analytic realization of the cleared q-series comparison in CDT v2
Section 11.1. This file transfers the exact formal numerator to a convergent
power-series expansion; the modular-form vanishing step is separate.
-/

namespace DirichletL

open Filter
open scoped Topology NNReal ENNReal

/-- The rational coefficient lift of a positive-scale q-Euler product. -/
noncomputable def qEulerProductSeriesRat (d : ℕ) : PowerSeries ℚ :=
  PowerSeries.map (Int.castRingHom ℚ) (qEulerProductSeries d)

/-- The rational case-C square numerator series. -/
noncomputable def caseCSquareNumeratorRat : PowerSeries ℚ :=
  qEulerProductSeriesRat 2 ^ 12 * qEulerProductSeriesRat 3 ^ 2

/-- The rational case-C square denominator series. -/
noncomputable def caseCSquareDenominatorRat : PowerSeries ℚ :=
  qEulerProductSeriesRat 1 ^ 6 * qEulerProductSeriesRat 6 ^ 4

/-- The rational shifted Hauptmodul series with its leading `X` removed. -/
noncomputable def hauptmodulShiftRat : PowerSeries ℚ :=
  PowerSeries.map (Int.castRingHom ℚ) hauptmodulShift

/-- The rational lift of the polynomial factor `1 - 10H + 9H^2`. -/
noncomputable def hauptmodulKRat : PowerSeries ℚ :=
  PowerSeries.map (Int.castRingHom ℚ) hauptmodulK

/-- The rational lift of the formal cleared derivative numerator. -/
noncomputable def hauptmodulDerivativeClearedNumeratorRat : PowerSeries ℚ :=
  PowerSeries.map (Int.castRingHom ℚ) hauptmodulDerivativeClearedNumerator

theorem caseCSquareNumeratorRat_eq_map :
    caseCSquareNumeratorRat =
      PowerSeries.map (Int.castRingHom ℚ) caseCSquareNumerator := by
  simp [caseCSquareNumeratorRat, caseCSquareNumerator, qEulerProductSeriesRat]

theorem caseCSquareDenominatorRat_eq_map :
    caseCSquareDenominatorRat =
      PowerSeries.map (Int.castRingHom ℚ) caseCSquareDenominator := by
  simp [caseCSquareDenominatorRat, caseCSquareDenominator, qEulerProductSeriesRat]

theorem hasFPowerSeriesAt_qEulerProductSeries_eval {d : ℕ} (hd : 0 < d) :
    HasFPowerSeriesAt (fun q : ℂ => qEulerProduct (q ^ d))
      (complexSeries (qEulerProductSeriesRat d)) 0 := by
  apply hasFPowerSeriesAt_of_eventually_hasSum
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4)]
    with q hq
  exact hasSum_qEulerProductSeries hd (by simpa using hq)

theorem hasFPowerSeriesAt_caseCSquareNumerator :
    HasFPowerSeriesAt
      (fun q : ℂ => qEulerProduct (q ^ 2) ^ 12 * qEulerProduct (q ^ 3) ^ 2)
      (complexSeries caseCSquareNumeratorRat) 0 := by
  simpa only [caseCSquareNumeratorRat, Function.comp_apply] using
    hasFPowerSeriesAt_powerSeries_mul
      (hasFPowerSeriesAt_powerSeries_pow
        (hasFPowerSeriesAt_qEulerProductSeries_eval (by norm_num : 0 < (2 : ℕ))) 12)
      (hasFPowerSeriesAt_powerSeries_pow
        (hasFPowerSeriesAt_qEulerProductSeries_eval (by norm_num : 0 < (3 : ℕ))) 2)

theorem hasFPowerSeriesAt_caseCSquareDenominator :
    HasFPowerSeriesAt
      (fun q : ℂ => qEulerProduct q ^ 6 * qEulerProduct (q ^ 6) ^ 4)
      (complexSeries caseCSquareDenominatorRat) 0 := by
  have h := hasFPowerSeriesAt_powerSeries_mul
      (hasFPowerSeriesAt_powerSeries_pow
        (hasFPowerSeriesAt_qEulerProductSeries_eval (by norm_num : 0 < (1 : ℕ))) 6)
      (hasFPowerSeriesAt_powerSeries_pow
        (hasFPowerSeriesAt_qEulerProductSeries_eval (by norm_num : 0 < (6 : ℕ))) 4)
  simpa only [caseCSquareDenominatorRat, Function.comp_apply, pow_one] using h

theorem formalShift_map_hauptmodul :
    formalShift (PowerSeries.map (Int.castRingHom ℚ) hauptmodul) = hauptmodulShiftRat := by
  ext n
  simp [hauptmodulShiftRat, formalShift, hauptmodulShift, PowerSeries.coeff_mk,
    PowerSeries.coeff_map, Int.coe_castRingHom, Rat.cast_intCast]

theorem hasFPowerSeriesAt_hauptmodulShift :
    HasFPowerSeriesAt (dslope hauptmodulProduct 0)
      (complexSeries hauptmodulShiftRat) 0 := by
  rw [← formalShift_map_hauptmodul]
  obtain ⟨r, hr⟩ := hasFPowerSeriesAt_hauptmodulProduct
  exact (hasFPowerSeriesOnBall_dslope hr).hasFPowerSeriesAt

theorem hasFPowerSeriesAt_hauptmodulDerivativeNumeratorRat :
    HasFPowerSeriesAt
      (fun q : ℂ => dslope hauptmodulProduct 0 q +
        q * deriv (dslope hauptmodulProduct 0) q)
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ)
        hauptmodulDerivativeNumerator)) 0 := by
  obtain ⟨r, hr⟩ := hasFPowerSeriesAt_hauptmodulProduct
  have hs : HasFPowerSeriesOnBall (dslope hauptmodulProduct 0)
      (complexSeries hauptmodulShiftRat) 0 r := by
    rw [← formalShift_map_hauptmodul]
    exact hasFPowerSeriesOnBall_dslope hr
  have hd := hasFPowerSeriesOnBall_derivativeFun hs
  have hm := hasFPowerSeriesAt_powerSeries_mul hasFPowerSeriesAt_complexSeries_X hd.hasFPowerSeriesAt
  have ha := hs.hasFPowerSeriesAt.add hm
  have hderivMap :
      (PowerSeries.map (Int.castRingHom ℚ) hauptmodulShift).derivativeFun =
        PowerSeries.map (Int.castRingHom ℚ) hauptmodulShift.derivativeFun := by
    ext n
    simp [PowerSeries.coeff_derivativeFun, PowerSeries.coeff_map,
      Int.coe_castRingHom, Rat.cast_intCast]
  have hformal : PowerSeries.map (Int.castRingHom ℚ) hauptmodulDerivativeNumerator =
      hauptmodulShiftRat + PowerSeries.X * hauptmodulShiftRat.derivativeFun := by
    ext n
    simp [hauptmodulDerivativeNumerator, hauptmodulShiftRat,
      PowerSeries.coeff_map, Int.coe_castRingHom, Rat.cast_intCast,
      PowerSeries.coeff_derivativeFun]
    rw [hderivMap]
  convert ha using 1
  · rw [hformal]
    ext n v
    simp [complexSeries, FormalMultilinearSeries.ofScalars]

theorem hasFPowerSeriesAt_hauptmodulKRat :
    HasFPowerSeriesAt (fun q : ℂ => 1 - 10 * hauptmodulProduct q +
        9 * hauptmodulProduct q ^ 2) (complexSeries hauptmodulKRat) 0 := by
  have hH := hasFPowerSeriesAt_hauptmodulProduct
  have hH2 := hasFPowerSeriesAt_powerSeries_pow hH 2
  have hneg := hH.const_smul (c := (-10 : ℂ))
  have hpos := hH2.const_smul (c := (9 : ℂ))
  have hconst : HasFPowerSeriesAt (fun _ : ℂ => (1 : ℂ))
      (constFormalMultilinearSeries ℂ ℂ (1 : ℂ)) (0 : ℂ) :=
    hasFPowerSeriesAt_const
  have hsum := (hconst.add hneg).add hpos
  have hformal : hauptmodulKRat =
      (1 : PowerSeries ℚ) - 10 * PowerSeries.map (Int.castRingHom ℚ) hauptmodul +
        9 * (PowerSeries.map (Int.castRingHom ℚ) hauptmodul) ^ 2 := by
    ext n
    simp [hauptmodulKRat, hauptmodulK, PowerSeries.coeff_map,
      Int.coe_castRingHom, Rat.cast_intCast, nsmul_eq_mul, map_ofNat]
  have hmap (n : ℕ) :
      PowerSeries.coeff (R := ℚ) n (PowerSeries.map (Int.castRingHom ℚ) hauptmodul) =
        (PowerSeries.coeff (R := ℤ) n hauptmodul : ℚ) := by
    simp [PowerSeries.coeff_map, Int.coe_castRingHom, Rat.cast_intCast]
  have hten (n : ℕ) :
      PowerSeries.coeff (R := ℚ) n (10 * PowerSeries.map (Int.castRingHom ℚ) hauptmodul) =
        10 * PowerSeries.coeff (R := ℚ) n (PowerSeries.map (Int.castRingHom ℚ) hauptmodul) := by
    change PowerSeries.coeff (R := ℚ) n
        (PowerSeries.C (R := ℚ) 10 * PowerSeries.map (Int.castRingHom ℚ) hauptmodul) = _
    rw [PowerSeries.coeff_C_mul]
  have hnine (n : ℕ) :
      PowerSeries.coeff (R := ℚ) n (9 * PowerSeries.map (Int.castRingHom ℚ) hauptmodul ^ 2) =
        9 * PowerSeries.coeff (R := ℚ) n (PowerSeries.map (Int.castRingHom ℚ) hauptmodul ^ 2) := by
    change PowerSeries.coeff (R := ℚ) n
        (PowerSeries.C (R := ℚ) 9 * (PowerSeries.map (Int.castRingHom ℚ) hauptmodul) ^ 2) = _
    rw [PowerSeries.coeff_C_mul]
  have hmap0 : PowerSeries.constantCoeff (R := ℚ)
      (PowerSeries.map (Int.castRingHom ℚ) hauptmodul) =
        (PowerSeries.constantCoeff (R := ℤ) hauptmodul : ℚ) := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hmap 0
  convert hsum using 1
  · ext q
    simp [smul_eq_mul]
    ring
  · rw [hformal]
    ext n v
    cases n with
    | zero => simp [complexSeries, FormalMultilinearSeries.ofScalars,
        constFormalMultilinearSeries, smul_eq_mul, map_ofNat,
        PowerSeries.coeff_map, Int.coe_castRingHom, Rat.cast_intCast,
        PowerSeries.coeff_C_mul, hmap, hmap0, hten, hnine] <;> ring
    | succ n =>
      simp [complexSeries, FormalMultilinearSeries.ofScalars,
        constFormalMultilinearSeries, smul_eq_mul, map_ofNat,
      PowerSeries.coeff_map, Int.coe_castRingHom, Rat.cast_intCast,
        PowerSeries.coeff_C_mul, hmap, hmap0, hten, hnine] <;> ring

/-- The local analytic cleared numerator in the q-coordinate. -/
noncomputable def hauptmodulDerivativeClearedNumeratorAnalytic (q : ℂ) : ℂ :=
  (dslope hauptmodulProduct 0 q + q * deriv (dslope hauptmodulProduct 0) q) *
      (qEulerProduct q ^ 6 * qEulerProduct (q ^ 6) ^ 4) -
    (1 - 10 * hauptmodulProduct q + 9 * hauptmodulProduct q ^ 2) *
      (qEulerProduct (q ^ 2) ^ 12 * qEulerProduct (q ^ 3) ^ 2) *
      dslope hauptmodulProduct 0 q

theorem hasFPowerSeriesAt_hauptmodulDerivativeClearedNumeratorRat :
    HasFPowerSeriesAt hauptmodulDerivativeClearedNumeratorAnalytic
      (complexSeries hauptmodulDerivativeClearedNumeratorRat) 0 := by
  have hleft := hasFPowerSeriesAt_powerSeries_mul
    hasFPowerSeriesAt_hauptmodulDerivativeNumeratorRat
    hasFPowerSeriesAt_caseCSquareDenominator
  have hright := hasFPowerSeriesAt_powerSeries_mul
    (hasFPowerSeriesAt_powerSeries_mul hasFPowerSeriesAt_hauptmodulKRat
      hasFPowerSeriesAt_caseCSquareNumerator)
    hasFPowerSeriesAt_hauptmodulShift
  have h := hleft.sub hright
  have hformal : hauptmodulDerivativeClearedNumeratorRat =
      (PowerSeries.map (Int.castRingHom ℚ) hauptmodulDerivativeNumerator) *
          caseCSquareDenominatorRat -
        ((hauptmodulKRat * caseCSquareNumeratorRat) * hauptmodulShiftRat) := by
    rw [caseCSquareNumeratorRat_eq_map, caseCSquareDenominatorRat_eq_map]
    simp [hauptmodulDerivativeClearedNumeratorRat,
      hauptmodulDerivativeClearedNumerator, hauptmodulKRat,
      hauptmodulK, hauptmodulShiftRat, map_sub, map_add, map_mul, map_pow,
      nsmul_eq_mul]
  convert h using 1
  · rw [hformal]
    ext n v
    simp [complexSeries, FormalMultilinearSeries.ofScalars]

theorem coeff_zero_hauptmodulDerivativeClearedNumeratorRat (m : ℕ) (hm : m < 3) :
    (complexSeries hauptmodulDerivativeClearedNumeratorRat).coeff m = 0 := by
  have h := coeffs_hauptmodulDerivativeClearedNumerator
  have h0 : PowerSeries.coeff (R := ℤ) 0 hauptmodulDerivativeClearedNumerator = 0 :=
    congrArg Prod.fst h
  have h1 : PowerSeries.coeff (R := ℤ) 1 hauptmodulDerivativeClearedNumerator = 0 :=
    congrArg (fun p => p.2.1) h
  have h2 : PowerSeries.coeff (R := ℤ) 2 hauptmodulDerivativeClearedNumerator = 0 :=
    congrArg (fun p => p.2.2) h
  interval_cases m <;>
    simp [coeff_complexSeries, hauptmodulDerivativeClearedNumeratorRat,
      PowerSeries.coeff_map, Int.coe_castRingHom, Rat.cast_intCast, h0, h1, h2]

theorem tendsto_div_cube_hauptmodulDerivativeClearedNumeratorAnalytic :
    Tendsto (fun q : ℂ => hauptmodulDerivativeClearedNumeratorAnalytic q / q ^ 3)
      (𝓝[≠] 0) (𝓝 ((complexSeries hauptmodulDerivativeClearedNumeratorRat).coeff 3)) :=
  tendsto_div_pow_of_hasFPowerSeriesAt
    hasFPowerSeriesAt_hauptmodulDerivativeClearedNumeratorRat
    coeff_zero_hauptmodulDerivativeClearedNumeratorRat

end DirichletL

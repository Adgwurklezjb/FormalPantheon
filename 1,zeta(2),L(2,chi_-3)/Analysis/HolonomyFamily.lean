import Analysis.FunctionsGFourteenIndependence
import Analysis.FunctionsGDenominators
import Analysis.PureFunctionDenominators
import Analysis.Holonomy

/-!
The literal family in the order used by CDT v2, `typesA` and its application
(supplied TeX 8280-8331): expansions, independence, and coefficient clearing.
The offset six is recorded explicitly; no holonomy dimension estimate or
offset-removal limit is asserted here.
-/

namespace DirichletL

open scoped Topology

/-- The rational expansions in the order of CDT's Lemma `14functions`. -/
noncomputable def cdtFourteenSeries (a b c : ℚ) : Fin 14 → PowerSeries ℚ :=
  Fin.append (zagierAuxiliarySeries (symmetrizedDescent (a • hA + b • hB + c • hC)))
    ![1, pureB2Series, pureB3Series, pureB4Series, pureB5Series, pureB6Series, pureB7Series]

theorem hasFPowerSeriesAt_cdtFourteenFamily (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (i : Fin 14) :
    HasFPowerSeriesAt (cdtFourteenFamily a b c i) (complexSeries (cdtFourteenSeries a b c i)) 0 := by
  have hr := pos_radius_complexSeries_symmetrizedDescent (a • hA + b • hB + c • hC)
    (zero_lt_one.trans_le (one_le_radius_h_linearCombination a b c hrel))
  have h (j : Fin 7) :=
    (hasFPowerSeriesOnBall_zagierAuxiliary _ hr le_rfl j).hasFPowerSeriesAt
  have h0 : HasFPowerSeriesAt (fun _ : ℂ => 1) (complexSeries (1 : PowerSeries ℚ)) 0 := by
    simpa using hasFPowerSeriesAt_int_const 1
  fin_cases i
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3
  · exact h 4
  · exact h 5
  · exact h 6
  · exact h0
  · exact hasFPowerSeriesOnBall_pureB2.hasFPowerSeriesAt
  · exact hasFPowerSeriesOnBall_pureB3.hasFPowerSeriesAt
  · exact hasFPowerSeriesAt_pureB4
  · exact hasFPowerSeriesOnBall_pureB5.hasFPowerSeriesAt
  · exact hasFPowerSeriesOnBall_pureB6.hasFPowerSeriesAt
  · exact hasFPowerSeriesAt_pureB7

/-- The zero-based permutation from `14functions` to the rows of `typesA`. -/
def cdtHolonomyOrder : Fin 14 → Fin 14 := ![7, 8, 9, 10, 11, 3, 4, 5, 6, 12, 13, 0, 1, 2]

theorem cdtHolonomyOrder_injective : Function.Injective cdtHolonomyOrder := by decide

/-- The analytic functions in the denominator-array order. -/
noncomputable def cdtHolonomyFamily (a b c : ℚ) : Fin 14 → ℂ → ℂ :=
  cdtFourteenFamily a b c ∘ cdtHolonomyOrder

/-- The formal rational expansions in the same denominator-array order. -/
noncomputable def cdtHolonomySeries (a b c : ℚ) : Fin 14 → PowerSeries ℚ :=
  cdtFourteenSeries a b c ∘ cdtHolonomyOrder

theorem hasFPowerSeriesAt_cdtHolonomyFamily (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (i : Fin 14) :
    HasFPowerSeriesAt (cdtHolonomyFamily a b c i) (complexSeries (cdtHolonomySeries a b c i)) 0 :=
  hasFPowerSeriesAt_cdtFourteenFamily a b c hrel (cdtHolonomyOrder i)

theorem linearIndependent_cdtHolonomyFamily (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    letI := (ratFuncEvalGerm 0).toModule
    LinearIndependent (RatFunc ℂ)
      (fun i : Fin 14 => (cdtHolonomyFamily a b c i : Filter.Germ (𝓝[≠] (0 : ℂ)) ℂ)) := by
  letI := (ratFuncEvalGerm 0).toModule
  exact (linearIndependent_cdtFourteenFamily a b c hrel hne).comp
    cdtHolonomyOrder cdtHolonomyOrder_injective

/-- A clearing multiplier with the exact integration exponents and fixed offsets. -/
def cdtHolonomyClearingMultiplier (i : Fin 14) (n : ℕ) : ℕ :=
  n ^ cdtIntegrationExponents ((i : ℕ) + 1) *
    if i = 0 then 1 else if (i : ℕ) < 3 then lcmPrefix (2 * n) else lcmPrefix (2 * n + 6) ^ 2

theorem cdtHolonomyClearingMultiplier_eq_array (i : Fin 14) (n : ℕ) :
    cdtHolonomyClearingMultiplier i n = n ^ cdtIntegrationExponents ((i : ℕ) + 1) *
      ∏ j ∈ Finset.range 2,
        lcmPrefix (⌊cdtDenominator14 ((i : ℕ) + 1) (j + 1) * (n : ℝ)⌋₊ +
          if (i : ℕ) < 3 then 0 else 6) := by
  have hf : ⌊(2 : ℝ) * (n : ℝ)⌋₊ = 2 * n := by
    rw [show (2 : ℝ) * (n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; rfl,
      Nat.floor_natCast]
  fin_cases i <;>
    simp [cdtHolonomyClearingMultiplier, cdtDenominator14, cdtIntegrationExponents,
      Finset.prod_range_succ, hf, lcmPrefix_zero, pow_two]

theorem isInteger_cdtHolonomySeries (a b c : ℤ) (i : Fin 14) (n : ℕ) :
    IsLocalization.IsInteger ℤ ((cdtHolonomyClearingMultiplier i n : ℚ) *
      PowerSeries.coeff (R := ℚ) n (cdtHolonomySeries a b c i)) := by
  have hG := isInteger_nat_pow_mul_lcmPrefix_sq_mul_coeff_GAuxiliary a b c
  have h4 : IsLocalization.IsInteger ℤ
      (((lcmPrefix (2 * n + 6) ^ 2 : ℕ) : ℚ) * PowerSeries.coeff (R := ℚ) n pureB4Series) := by
    simpa only [Nat.cast_pow] using (sqIntegral_iff_isInteger _ _).mp
      ((sqIntegral_coeff_pureB4Series n).of_dvd (lcmPrefix_dvd (by omega)))
  have h5 : IsLocalization.IsInteger ℤ
      (((lcmPrefix (2 * n + 6) ^ 2 : ℕ) : ℚ) * PowerSeries.coeff (R := ℚ) n pureB5Series) := by
    simpa only [Nat.cast_pow] using (sqIntegral_iff_isInteger _ _).mp
      ((sqIntegral_coeff_pureB5Series n).of_dvd (lcmPrefix_dvd (by omega)))
  have hd : n * lcmPrefix (2 * n) ^ 2 ∣ n * lcmPrefix (2 * n + 6) ^ 2 :=
    Nat.mul_dvd_mul_left n (pow_dvd_pow_of_dvd (lcmPrefix_dvd (by omega)) 2)
  have h6 := isInteger_nat_mul_of_dvd
    (isInteger_nat_mul_lcmPrefix_sq_mul_coeff_pureB6Series n) hd
  have h7 := isInteger_nat_mul_of_dvd
    (isInteger_nat_mul_lcmPrefix_sq_mul_coeff_pureB7Series n) hd
  fin_cases i
  · change IsLocalization.IsInteger ℤ ((1 : ℚ) *
      PowerSeries.coeff (R := ℚ) n (1 : PowerSeries ℚ))
    rw [one_mul, PowerSeries.coeff_one]
    split_ifs
    · exact IsLocalization.isInteger_one
    · exact IsLocalization.isInteger_zero
  · simpa [cdtHolonomyClearingMultiplier, cdtIntegrationExponents, cdtHolonomySeries,
      cdtFourteenSeries, cdtHolonomyOrder, Fin.append] using
      isInteger_lcmPrefix_mul_coeff_pureB2Series n
  · simpa [cdtHolonomyClearingMultiplier, cdtIntegrationExponents, cdtHolonomySeries,
      cdtFourteenSeries, cdtHolonomyOrder, Fin.append] using
      isInteger_nat_mul_lcmPrefix_mul_coeff_pureB3Series n
  · simpa [cdtHolonomyClearingMultiplier, cdtIntegrationExponents, cdtHolonomySeries,
      cdtFourteenSeries, cdtHolonomyOrder, Fin.append] using h4
  · simpa [cdtHolonomyClearingMultiplier, cdtIntegrationExponents, cdtHolonomySeries,
      cdtFourteenSeries, cdtHolonomyOrder, Fin.append] using h5
  · simpa [cdtHolonomyClearingMultiplier, cdtIntegrationExponents, cdtHolonomySeries,
      cdtFourteenSeries, cdtHolonomyOrder, Fin.append] using hG 3 n
  · simpa [cdtHolonomyClearingMultiplier, cdtIntegrationExponents, cdtHolonomySeries,
      cdtFourteenSeries, cdtHolonomyOrder, Fin.append] using hG 4 n
  · simpa [cdtHolonomyClearingMultiplier, cdtIntegrationExponents, cdtHolonomySeries,
      cdtFourteenSeries, cdtHolonomyOrder, Fin.append] using hG 5 n
  · simpa [cdtHolonomyClearingMultiplier, cdtIntegrationExponents, cdtHolonomySeries,
      cdtFourteenSeries, cdtHolonomyOrder, Fin.append] using hG 6 n
  · simpa [cdtHolonomyClearingMultiplier, cdtIntegrationExponents, cdtHolonomySeries,
      cdtFourteenSeries, cdtHolonomyOrder, Fin.append] using h6
  · simpa [cdtHolonomyClearingMultiplier, cdtIntegrationExponents, cdtHolonomySeries,
      cdtFourteenSeries, cdtHolonomyOrder, Fin.append] using h7
  · simpa [cdtHolonomyClearingMultiplier, cdtIntegrationExponents, cdtHolonomySeries,
      cdtFourteenSeries, cdtHolonomyOrder, Fin.append] using hG 0 n
  · simpa [cdtHolonomyClearingMultiplier, cdtIntegrationExponents, cdtHolonomySeries,
      cdtFourteenSeries, cdtHolonomyOrder, Fin.append] using hG 1 n
  · simpa [cdtHolonomyClearingMultiplier, cdtIntegrationExponents, cdtHolonomySeries,
      cdtFourteenSeries, cdtHolonomyOrder, Fin.append] using hG 2 n

end DirichletL

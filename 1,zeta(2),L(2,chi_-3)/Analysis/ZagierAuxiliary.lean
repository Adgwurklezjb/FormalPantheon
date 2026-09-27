import Analysis.AnalyticIntegrals
import Analysis.MobiusDescentAnalytic

/-!
The ordered seven Zagier functions in CDT v2, Lemma `14functions`.
This module constructs their local analytic expansions and the regularized
`G_A` family's coefficient bounds; their functional independence remains to be proved.
-/

namespace DirichletL

open scoped ENNReal

/-- The three regularized formal primitives, the input, and its first three derivatives. -/
noncomputable def zagierAuxiliarySeries (f : PowerSeries ℚ) : Fin 7 → PowerSeries ℚ :=
  ![formalIntegral f, formalIntegral (formalShift f), formalIntegral (formalSecondShift f),
    f, f.derivativeFun, f.derivativeFun.derivativeFun,
    f.derivativeFun.derivativeFun.derivativeFun]

/-- The analytic functions in the same order as `zagierAuxiliarySeries`. -/
noncomputable def zagierAuxiliaryFunctions (f : PowerSeries ℚ) : Fin 7 → ℂ → ℂ :=
  ![analyticIntegral f, analyticIntegral (formalShift f), analyticIntegral (formalSecondShift f),
    (complexSeries f).sum, deriv (complexSeries f).sum, deriv (deriv (complexSeries f).sum),
    deriv (deriv (deriv (complexSeries f).sum))]

/-- Every member has its prescribed rational expansion on the input convergence ball. -/
theorem hasFPowerSeriesOnBall_zagierAuxiliary (f : PowerSeries ℚ) {r : ℝ≥0∞}
    (hr0 : 0 < r) (hr : r ≤ (complexSeries f).radius) (i : Fin 7) :
    HasFPowerSeriesOnBall (zagierAuxiliaryFunctions f i)
      (complexSeries (zagierAuxiliarySeries f i)) 0 r := by
  have hF := ((complexSeries f).hasFPowerSeriesOnBall (hr0.trans_le hr)).mono hr0 hr
  have hd1 := hasFPowerSeriesOnBall_derivativeFun hF
  have hd2 := hasFPowerSeriesOnBall_derivativeFun hd1
  have hd3 := hasFPowerSeriesOnBall_derivativeFun hd2
  fin_cases i
  · exact hasFPowerSeriesOnBall_analyticIntegral f hr0 hr
  · exact hasFPowerSeriesOnBall_analyticIntegral (formalShift f) hr0
      (by simpa [radius_complexSeries_formalShift] using hr)
  · exact hasFPowerSeriesOnBall_analyticIntegral (formalSecondShift f) hr0
      (by simpa [radius_complexSeries_formalSecondShift] using hr)
  · exact hF
  · exact hd1
  · exact hd2
  · exact hd3

theorem analyticAt_zagierAuxiliaryFunctions (f : PowerSeries ℚ) {r : ℝ≥0∞}
    (hr0 : 0 < r) (hr : r ≤ (complexSeries f).radius) (i : Fin 7)
    {z : ℂ} (hz : z ∈ EMetric.ball 0 r) :
    AnalyticAt ℂ (zagierAuxiliaryFunctions f i) z :=
  (hasFPowerSeriesOnBall_zagierAuxiliary f hr0 hr i).analyticAt_of_mem hz

/-- The three primitives use zero integration constants. -/
theorem zagierAuxiliaryFunctions_integrals_zero (f : PowerSeries ℚ) (i : Fin 3) :
    zagierAuxiliaryFunctions f (i.castAdd 4) 0 = 0 := by
  fin_cases i <;> simp [zagierAuxiliaryFunctions]

/-- The first three derivatives are the source integrands, with their removable values at zero. -/
theorem hasDerivAt_zagierAuxiliaryFunctions_integrals (f : PowerSeries ℚ) {r : ℝ≥0∞}
    (hr0 : 0 < r) (hr : r ≤ (complexSeries f).radius) (i : Fin 3)
    {z : ℂ} (hz : z ∈ EMetric.ball 0 r) :
    HasDerivAt (zagierAuxiliaryFunctions f (i.castAdd 4))
      (![(complexSeries f).sum, dslope (complexSeries f).sum 0,
        dslope (dslope (complexSeries f).sum 0) 0] i z) z := by
  have hF := ((complexSeries f).hasFPowerSeriesOnBall (hr0.trans_le hr)).mono hr0 hr
  fin_cases i
  · exact hasDerivAt_analyticIntegral hF hz
  · exact hasDerivAt_analyticIntegral (hasFPowerSeriesOnBall_dslope hF) hz
  · exact hasDerivAt_analyticIntegral (hasFPowerSeriesOnBall_dslope_dslope hF) hz

theorem deriv_zagierAuxiliaryFunctions_one (f : PowerSeries ℚ) {r : ℝ≥0∞}
    (hr0 : 0 < r) (hr : r ≤ (complexSeries f).radius)
    {z : ℂ} (hz : z ∈ EMetric.ball 0 r) (hz0 : z ≠ 0) :
    deriv (zagierAuxiliaryFunctions f 1) z =
      ((complexSeries f).sum z - (complexSeries f).sum 0) / z := by
  have hd := (hasDerivAt_zagierAuxiliaryFunctions_integrals f hr0 hr 1 hz).deriv
  change deriv (zagierAuxiliaryFunctions f 1) z = dslope (complexSeries f).sum 0 z at hd
  rw [hd, dslope_of_ne _ hz0]
  simp [slope, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem deriv_zagierAuxiliaryFunctions_two (f : PowerSeries ℚ) {r : ℝ≥0∞}
    (hr0 : 0 < r) (hr : r ≤ (complexSeries f).radius)
    {z : ℂ} (hz : z ∈ EMetric.ball 0 r) (hz0 : z ≠ 0) :
    deriv (zagierAuxiliaryFunctions f 2) z =
      ((complexSeries f).sum z - (complexSeries f).sum 0 -
        deriv (complexSeries f).sum 0 * z) / z ^ 2 := by
  have hd := (hasDerivAt_zagierAuxiliaryFunctions_integrals f hr0 hr 2 hz).deriv
  change deriv (zagierAuxiliaryFunctions f 2) z =
    dslope (dslope (complexSeries f).sum 0) 0 z at hd
  rw [hd]
  simp only [dslope_of_ne _ hz0, dslope_same, slope, vsub_eq_sub, sub_zero, smul_eq_mul]
  field_simp

/-- The regularized `G_A` family exists on its verified disk. -/
theorem hasFPowerSeriesOnBall_zagierAuxiliary_hA (i : Fin 7) :
    HasFPowerSeriesOnBall (zagierAuxiliaryFunctions (symmetrizedDescent hA) i)
      (complexSeries (zagierAuxiliarySeries (symmetrizedDescent hA) i)) 0
      (1 / 648 : ℝ≥0∞) := by
  exact hasFPowerSeriesOnBall_zagierAuxiliary _
    hasFPowerSeriesOnBall_symmetrizedAnalytic_hA.r_pos
    hasFPowerSeriesOnBall_symmetrizedAnalytic_hA.r_le i

theorem analyticAt_zagierAuxiliary_hA (i : Fin 7) {z : ℂ} (hz : ‖z‖ < 1 / 648) :
    AnalyticAt ℂ (zagierAuxiliaryFunctions (symmetrizedDescent hA) i) z := by
  apply (hasFPowerSeriesOnBall_zagierAuxiliary_hA i).analyticAt_of_mem
  rw [EMetric.mem_ball, edist_zero_right, ← ofReal_norm_eq_enorm]
  have hr : ENNReal.ofReal (1 / 648 : ℝ) = (1 / 648 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  rw [← hr]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 648)).mpr hz

private theorem int_coeff_formalShift {f : PowerSeries ℚ}
    (hf : ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff (R := ℚ) n f = z) :
    ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff (R := ℚ) n (formalShift f) = z := by
  intro n
  simpa using hf (n + 1)

private theorem int_coeff_formalSecondShift {f : PowerSeries ℚ}
    (hf : ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff (R := ℚ) n f = z) :
    ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff (R := ℚ) n (formalSecondShift f) = z := by
  intro n
  simpa using hf (n + 2)

private theorem int_coeff_derivativeFun {f : PowerSeries ℚ}
    (hf : ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff (R := ℚ) n f = z) :
    ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff (R := ℚ) n f.derivativeFun = z := by
  intro n
  obtain ⟨z, hz⟩ := hf (n + 1)
  refine ⟨(n + 1 : ℤ) * z, ?_⟩
  simp [PowerSeries.coeff_derivativeFun, hz, nsmul_eq_mul, mul_comm]

private theorem int_lcm_mul_coeff_formalIntegral {f : PowerSeries ℚ}
    (hf : ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff (R := ℚ) n f = z) (n : ℕ) :
    ∃ z : ℤ, (lcmPrefix n : ℚ) * PowerSeries.coeff (R := ℚ) n (formalIntegral f) = z := by
  cases n with
  | zero => exact ⟨0, by simp⟩
  | succ n =>
    obtain ⟨z, hz⟩ := hf n
    obtain ⟨k, hk⟩ := succ_dvd_lcmPrefix_succ n
    refine ⟨(k : ℤ) * z, ?_⟩
    rw [coeff_formalIntegral_succ, hz, hk]
    push_cast
    field_simp

/-- Integral input needs a single prefix-lcm factor only for the three primitive entries. -/
theorem exists_int_mul_coeff_zagierAuxiliarySeries {f : PowerSeries ℚ}
    (hf : ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff (R := ℚ) n f = z) (i : Fin 7) (n : ℕ) :
    ∃ z : ℤ, (if i.val < 3 then (lcmPrefix n : ℚ) else 1) *
      PowerSeries.coeff (R := ℚ) n (zagierAuxiliarySeries f i) = z := by
  have hd1 := int_coeff_derivativeFun hf
  have hd2 := int_coeff_derivativeFun hd1
  have hd3 := int_coeff_derivativeFun hd2
  fin_cases i
  · exact int_lcm_mul_coeff_formalIntegral hf n
  · exact int_lcm_mul_coeff_formalIntegral (int_coeff_formalShift hf) n
  · exact int_lcm_mul_coeff_formalIntegral (int_coeff_formalSecondShift hf) n
  · simpa [zagierAuxiliarySeries] using hf n
  · simpa [zagierAuxiliarySeries] using hd1 n
  · simpa [zagierAuxiliarySeries] using hd2 n
  · simpa [zagierAuxiliarySeries] using hd3 n

theorem exists_int_mul_coeff_zagierAuxiliary_hA (i : Fin 7) (n : ℕ) :
    ∃ z : ℤ, (if i.val < 3 then (lcmPrefix n : ℚ) else 1) *
      PowerSeries.coeff (R := ℚ) n (zagierAuxiliarySeries (symmetrizedDescent hA) i) = z :=
  exists_int_mul_coeff_zagierAuxiliarySeries exists_int_coeff_symmetrizedDescent_hA i n

end DirichletL

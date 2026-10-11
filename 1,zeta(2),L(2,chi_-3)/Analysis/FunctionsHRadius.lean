import Analysis.FunctionsHFormalODE
import Analysis.FunctionsHAnalytic
import Analysis.ZagierEndpointSymmetry

/-!
The individual convergence radii in CDT v2 Section 11.1, Lemma `defabc`,
part (3), for the literal H_B and H_C series. Exact recurrence comparisons
replace the stronger general asymptotics for this subclaim only.
-/

namespace DirichletL

open scoped NNReal ENNReal

theorem hB_coeff_bounds (n : ℕ) :
    0 ≤ PowerSeries.coeff (R := ℚ) n hB ∧
      3 * PowerSeries.coeff (R := ℚ) n hB ≤ (n : ℚ) * (zagierC n : ℚ) ∧
        (1 ≤ n → (zagierC n : ℚ) ≤ 3 * PowerSeries.coeff (R := ℚ) n hB) := by
  apply zagier_recurrence_comparison (fun k => PowerSeries.coeff (R := ℚ) k hB) (fun _ => 0)
    (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hB_constantCoeff)
    hB_coeff_one (fun _ _ => by norm_num) hB_recurrence

theorem hC_coeff_bounds (n : ℕ) :
    0 ≤ PowerSeries.coeff (R := ℚ) n hC ∧
      3 * PowerSeries.coeff (R := ℚ) n hC ≤ (n : ℚ) * (zagierC n : ℚ) ∧
        (1 ≤ n → (zagierC n : ℚ) ≤ 3 * PowerSeries.coeff (R := ℚ) n hC) := by
  apply zagier_recurrence_comparison (fun k => PowerSeries.coeff (R := ℚ) k hC) (fun _ => 1)
    (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hC_constantCoeff)
    hC_coeff_one (fun _ _ => by norm_num) hC_recurrence

private theorem radius_eq_of_zagier_comparison (p : PowerSeries ℚ)
    (hp : ∀ n : ℕ, 0 ≤ PowerSeries.coeff (R := ℚ) n p ∧
      3 * PowerSeries.coeff (R := ℚ) n p ≤ (n : ℚ) * (zagierC n : ℚ) ∧
        (1 ≤ n → (zagierC n : ℚ) ≤ 3 * PowerSeries.coeff (R := ℚ) n p)) :
    (complexSeries p).radius = (1 / 9 : ℝ≥0∞) := by
  have hnorm (n : ℕ) : ‖complexSeries p n‖ = (PowerSeries.coeff (R := ℚ) n p : ℝ) := by
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef, coeff_complexSeries,
      Complex.norm_ratCast, abs_of_nonneg (by exact_mod_cast (hp n).1)]
  apply le_antisymm
  · have hcoeff (n : ℕ) :
        ‖(complexSeries zagierGenerating).shift n‖ ≤
          ‖((3 : ℂ) • complexSeries p).shift n‖ := by
      simp only [FormalMultilinearSeries.shift, ContinuousMultilinearMap.curryRight_norm,
        FormalMultilinearSeries.smul_apply]
      rw [norm_smul (3 : ℂ) (complexSeries p (n + 1)), Complex.norm_ofNat, hnorm]
      simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef, coeff_complexSeries,
        zagierGenerating, generatingSeries, PowerSeries.coeff_mk, Rat.cast_natCast,
        Complex.norm_natCast]
      exact_mod_cast (hp (n + 1)).2.2 (by omega)
    have h := FormalMultilinearSeries.radius_le_of_le hcoeff
    rw [FormalMultilinearSeries.radius_shift,
      FormalMultilinearSeries.radius_smul_eq _ (by norm_num : (3 : ℂ) ≠ 0),
      FormalMultilinearSeries.radius_shift, radius_complexSeries_zagierGenerating] at h
    exact h
  · apply ENNReal.le_of_forall_nnreal_lt
    intro r hr
    have hr' : (r : ℝ) < 1 / 9 := by
      have hcast : (r : ℝ≥0∞) < ((1 / 9 : ℝ≥0) : ℝ≥0∞) := by simpa using hr
      exact_mod_cast hcast
    have hq : ‖9 * (r : ℝ)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith
    have hsum := (summable_pow_mul_geometric_of_norm_lt_one 1 hq).div_const 3
    apply (complexSeries p).le_radius_of_summable
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (by positivity)) _ hsum
    intro n
    have hupper : ‖complexSeries p n‖ ≤ (n : ℝ) * 9 ^ n / 3 := by
      rw [hnorm]
      have h0 : 3 * (PowerSeries.coeff (R := ℚ) n p : ℝ) ≤ (n : ℝ) * (zagierC n : ℝ) := by
        exact_mod_cast (hp n).2.1
      have h1 : (zagierC n : ℝ) ≤ 9 ^ n := by exact_mod_cast zagierC_le_nine_pow n
      have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      linarith
    calc
      ‖complexSeries p n‖ * (r : ℝ) ^ n ≤ ((n : ℝ) * 9 ^ n / 3) * (r : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hupper (by positivity)
      _ = (n : ℝ) ^ 1 * (9 * (r : ℝ)) ^ n / 3 := by rw [mul_pow, pow_one]; ring

/-- The exact convergence radius of the literal B-series. -/
theorem radius_complexSeries_hB : (complexSeries hB).radius = (1 / 9 : ℝ≥0∞) :=
  radius_eq_of_zagier_comparison hB hB_coeff_bounds

/-- The exact convergence radius of the literal C-series. -/
theorem radius_complexSeries_hC : (complexSeries hC).radius = (1 / 9 : ℝ≥0∞) :=
  radius_eq_of_zagier_comparison hC hC_coeff_bounds

theorem hasFPowerSeriesOnBall_hBAnalytic :
    HasFPowerSeriesOnBall hBAnalytic (complexSeries hB) 0 (1 / 9 : ℝ≥0∞) := by
  simpa only [radius_complexSeries_hB] using
    ((complexSeries hB).hasFPowerSeriesOnBall pos_radius_complexSeries_hB)

theorem hasFPowerSeriesOnBall_hCAnalytic :
    HasFPowerSeriesOnBall hCAnalytic (complexSeries hC) 0 (1 / 9 : ℝ≥0∞) := by
  simpa only [radius_complexSeries_hC] using
    ((complexSeries hC).hasFPowerSeriesOnBall pos_radius_complexSeries_hC)

end DirichletL

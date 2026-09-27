import Analysis.FunctionsHRadius
import Analysis.ZagierCoefficientLimits

/-!
The coefficient-limit part of CDT v2, Section 11.1, Lemma `defabc` (3),
using the exact recurrence estimates recorded in
identified with the paper's special values in `FunctionsHSpecialValues.lean`.
-/

namespace DirichletL

open Filter
open scoped Topology NNReal ENNReal

private theorem le_radius_zagier_remainder (p : PowerSeries ℚ) (ℓ : ℝ)
    (hbound : ∀ n, |ℓ * (zagierC n : ℝ) - (PowerSeries.coeff (R := ℚ) n p : ℝ)| ≤
      8 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2) :
    (1 : ℝ≥0∞) ≤ (complexSeries p - (ℓ : ℂ) • complexSeries zagierGenerating).radius := by
  let s := complexSeries p - (ℓ : ℂ) • complexSeries zagierGenerating
  change (1 : ℝ≥0∞) ≤ s.radius
  have hnorm (n : ℕ) : ‖s n‖ = |ℓ * (zagierC n : ℝ) - (PowerSeries.coeff (R := ℚ) n p : ℝ)| := by
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef]
    have hc : s.coeff n = (complexSeries p).coeff n -
        (ℓ : ℂ) * (complexSeries zagierGenerating).coeff n := by
      simp only [s, FormalMultilinearSeries.coeff, FormalMultilinearSeries.sub_apply,
        FormalMultilinearSeries.smul_apply, ContinuousMultilinearMap.sub_apply,
        ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    rw [hc, coeff_complexSeries, coeff_complexSeries]
    simp only [zagierGenerating, generatingSeries, PowerSeries.coeff_mk, Rat.cast_natCast]
    have he : (PowerSeries.coeff (R := ℚ) n p : ℂ) - (ℓ : ℂ) * (zagierC n : ℂ) =
        (((PowerSeries.coeff (R := ℚ) n p : ℝ) - ℓ * (zagierC n : ℝ) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have hcoeff (n : ℕ) : ‖s n‖ ≤ 288 * ((n : ℝ) ^ 4 + 1) := by
    apply (hnorm n).trans_le ((hbound n).trans ?_)
    by_cases hn : n = 0
    · subst n
      norm_num
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      calc
        8 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2 ≤
            8 * (2 * (n : ℝ)) ^ 2 * (3 * (n : ℝ)) ^ 2 := by gcongr <;> linarith
        _ = 288 * (n : ℝ) ^ 4 := by ring
        _ ≤ _ := by linarith
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  have hr' : (r : ℝ) < 1 := by exact_mod_cast hr
  have hnormr : ‖(r : ℝ)‖ < 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg] using hr'
  have hsum := ((summable_pow_mul_geometric_of_norm_lt_one 4 hnormr).add
    (hasSum_geometric_of_norm_lt_one hnormr).summable).mul_left 288
  apply s.le_radius_of_summable
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (by positivity)) _ hsum
  intro n
  calc
    ‖s n‖ * (r : ℝ) ^ n ≤ (288 * ((n : ℝ) ^ 4 + 1)) * (r : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right (hcoeff n) (by positivity)
    _ = 288 * ((n : ℝ) ^ 4 * (r : ℝ) ^ n + (r : ℝ) ^ n) := by ring

/-- The literal B coefficients have a real limit and an error series of radius at least one. -/
theorem exists_hB_coefficient_limit :
    ∃ ℓ : ℝ, Tendsto (fun n => (PowerSeries.coeff (R := ℚ) n hB : ℝ) / (zagierC n : ℝ)) atTop (𝓝 ℓ) ∧
      (∀ n, |ℓ * (zagierC n : ℝ) - (PowerSeries.coeff (R := ℚ) n hB : ℝ)| ≤
        8 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2) ∧
      (1 : ℝ≥0∞) ≤ (complexSeries hB - (ℓ : ℂ) • complexSeries zagierGenerating).radius := by
  obtain ⟨ℓ, hℓ, hbound⟩ := exists_zagier_coefficient_limit
    (fun n => PowerSeries.coeff (R := ℚ) n hB)
    (zagierDiscreteWronskian_bounds _ (fun _ => 0)
      (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hB_constantCoeff)
      hB_coeff_one (fun _ _ => by norm_num) hB_recurrence)
  exact ⟨ℓ, hℓ, hbound, le_radius_zagier_remainder hB ℓ hbound⟩

/-- The literal C coefficients have a real limit and an error series of radius at least one. -/
theorem exists_hC_coefficient_limit :
    ∃ ℓ : ℝ, Tendsto (fun n => (PowerSeries.coeff (R := ℚ) n hC : ℝ) / (zagierC n : ℝ)) atTop (𝓝 ℓ) ∧
      (∀ n, |ℓ * (zagierC n : ℝ) - (PowerSeries.coeff (R := ℚ) n hC : ℝ)| ≤
        8 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2) ∧
      (1 : ℝ≥0∞) ≤ (complexSeries hC - (ℓ : ℂ) • complexSeries zagierGenerating).radius := by
  obtain ⟨ℓ, hℓ, hbound⟩ := exists_zagier_coefficient_limit
    (fun n => PowerSeries.coeff (R := ℚ) n hC)
    (zagierDiscreteWronskian_bounds _ (fun _ => 1)
      (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hC_constantCoeff)
      hC_coeff_one (fun _ _ => by norm_num) hC_recurrence)
  exact ⟨ℓ, hℓ, hbound, le_radius_zagier_remainder hC ℓ hbound⟩

end DirichletL

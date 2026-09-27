import Analysis.FormalIntegrals
import Analysis.PowerSeriesAnalytic

/-!
Analytic primitives and removable quotients for the first three functions
in CDT v2, Lemma `14functions`. All analytic assertions specify a convergence ball.
-/

namespace DirichletL

open scoped ENNReal

private theorem norm_complexSeries_shift (f : PowerSeries ℚ) (n : ℕ) :
    ‖(complexSeries f).shift n‖ = ‖(PowerSeries.coeff (R := ℚ) (n + 1) f : ℂ)‖ := by
  simp only [FormalMultilinearSeries.shift, ContinuousMultilinearMap.curryRight_norm,
    FormalMultilinearSeries.norm_apply_eq_norm_coef, coeff_complexSeries]

/-- Removing a constant coefficient and dividing by the variable preserves the radius. -/
theorem radius_complexSeries_formalShift (f : PowerSeries ℚ) :
    (complexSeries (formalShift f)).radius = (complexSeries f).radius := by
  have hn (n : ℕ) : ‖complexSeries (formalShift f) n‖ = ‖(complexSeries f).shift n‖ := by
    rw [norm_complexSeries_shift, FormalMultilinearSeries.norm_apply_eq_norm_coef,
      coeff_complexSeries, coeff_formalShift]
  rw [← (complexSeries f).radius_shift]
  exact le_antisymm (FormalMultilinearSeries.radius_le_of_le (fun n => (hn n).ge))
    (FormalMultilinearSeries.radius_le_of_le (fun n => (hn n).le))

theorem radius_complexSeries_formalSecondShift (f : PowerSeries ℚ) :
    (complexSeries (formalSecondShift f)).radius = (complexSeries f).radius := by
  rw [formalSecondShift_eq, radius_complexSeries_formalShift,
    radius_complexSeries_formalShift]

/-- Coefficientwise integration preserves every open ball of convergence. -/
theorem le_radius_complexSeries_formalIntegral (f : PowerSeries ℚ) :
    (complexSeries f).radius ≤ (complexSeries (formalIntegral f)).radius := by
  rw [← (complexSeries (formalIntegral f)).radius_shift]
  apply FormalMultilinearSeries.radius_le_of_le
  intro n
  rw [norm_complexSeries_shift, coeff_formalIntegral_succ,
    FormalMultilinearSeries.norm_apply_eq_norm_coef, coeff_complexSeries]
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, norm_div]
  have hn : (1 : ℝ) ≤ ‖(n : ℂ) + 1‖ := by
    rw [← Nat.cast_succ, Complex.norm_natCast]
    norm_cast
    omega
  exact div_le_self (norm_nonneg _) hn

/-- The canonical analytic primitive with zero constant term. -/
noncomputable def analyticIntegral (f : PowerSeries ℚ) : ℂ → ℂ :=
  (complexSeries (formalIntegral f)).sum

@[simp]
theorem analyticIntegral_zero (f : PowerSeries ℚ) : analyticIntegral f 0 = 0 := by
  change FormalMultilinearSeries.ofScalarsSum
    (fun n => (PowerSeries.coeff (R := ℚ) n (formalIntegral f) : ℂ)) 0 = 0
  simp [FormalMultilinearSeries.ofScalarsSum_zero]

theorem hasFPowerSeriesOnBall_analyticIntegral (f : PowerSeries ℚ) {r : ℝ≥0∞}
    (hr0 : 0 < r) (hr : r ≤ (complexSeries f).radius) :
    HasFPowerSeriesOnBall (analyticIntegral f) (complexSeries (formalIntegral f)) 0 r := by
  have hrad := hr.trans (le_radius_complexSeries_formalIntegral f)
  exact ((complexSeries (formalIntegral f)).hasFPowerSeriesOnBall
    (hr0.trans_le hrad)).mono hr0 hrad

/-- The normalized primitive differentiates to any function with the input expansion. -/
theorem hasDerivAt_analyticIntegral {F : ℂ → ℂ} {f : PowerSeries ℚ} {r : ℝ≥0∞}
    (hF : HasFPowerSeriesOnBall F (complexSeries f) 0 r)
    {z : ℂ} (hz : z ∈ EMetric.ball 0 r) :
    HasDerivAt (analyticIntegral f) (F z) z := by
  have hi := hasFPowerSeriesOnBall_analyticIntegral f hF.r_pos hF.r_le
  have hd := hasFPowerSeriesOnBall_derivativeFun hi
  rw [derivative_formalIntegral] at hd
  have heq : deriv (analyticIntegral f) z = F z := by
    simpa only [zero_add] using (hd.sum hz).trans (hF.sum hz).symm
  have h := (hi.analyticAt_of_mem hz).differentiableAt.hasDerivAt
  rwa [heq] at h

/-- The shifted rational series expands the canonical removable quotient on the same ball. -/
theorem hasFPowerSeriesOnBall_dslope {F : ℂ → ℂ} {f : PowerSeries ℚ} {r : ℝ≥0∞}
    (hF : HasFPowerSeriesOnBall F (complexSeries f) 0 r) :
    HasFPowerSeriesOnBall (dslope F 0) (complexSeries (formalShift f)) 0 r := by
  have hp0 : (PowerSeries.coeff (R := ℚ) 0 f : ℂ) = F 0 := by
    simpa [FormalMultilinearSeries.apply_eq_pow_smul_coeff, coeff_complexSeries]
      using hF.coeff_zero (fun _ => 1)
  have hp1 : deriv F 0 = (PowerSeries.coeff (R := ℚ) 1 f : ℂ) := by
    simpa [FormalMultilinearSeries.apply_eq_pow_smul_coeff, coeff_complexSeries]
      using hF.hasFPowerSeriesAt.deriv
  refine ⟨by simpa [radius_complexSeries_formalShift] using hF.r_le, hF.r_pos, ?_⟩
  intro z hz
  have hs := hasSum_of_hasFPowerSeriesOnBall hF hz
  have hsum : HasSum (fun n : ℕ => (PowerSeries.coeff (R := ℚ) (n + 1) f : ℂ) * z ^ n)
      (dslope F 0 z) := by
    by_cases hz0 : z = 0
    · subst z
      rw [dslope_same, hp1]
      simpa [smul_eq_mul, mul_comm] using
        (HasSum.hasSum_at_zero (𝕜 := ℂ) (fun n => (PowerSeries.coeff (R := ℚ) (n + 1) f : ℂ)))
    · have ht : HasSum (fun n : ℕ => (PowerSeries.coeff (R := ℚ) (n + 1) f : ℂ) * z ^ (n + 1))
          (F z - F 0) := by
        simpa only [Finset.sum_range_one, pow_zero, mul_one, hp0]
          using (hasSum_nat_add_iff' 1).mpr hs
      convert ht.mul_left z⁻¹ using 1
      · ext n
        field_simp [hz0]
        simp [pow_succ, mul_assoc]
      · rw [dslope_of_ne _ hz0]
        simp [slope, smul_eq_mul]
  simpa [complexSeries, FormalMultilinearSeries.ofScalars_apply_eq, coeff_formalShift,
    smul_eq_mul, mul_comm] using hsum

/-- Two regularized quotients remove the constant and linear terms. -/
theorem hasFPowerSeriesOnBall_dslope_dslope {F : ℂ → ℂ} {f : PowerSeries ℚ} {r : ℝ≥0∞}
    (hF : HasFPowerSeriesOnBall F (complexSeries f) 0 r) :
    HasFPowerSeriesOnBall (dslope (dslope F 0) 0)
      (complexSeries (formalSecondShift f)) 0 r := by
  rw [formalSecondShift_eq]
  exact hasFPowerSeriesOnBall_dslope (hasFPowerSeriesOnBall_dslope hF)

end DirichletL

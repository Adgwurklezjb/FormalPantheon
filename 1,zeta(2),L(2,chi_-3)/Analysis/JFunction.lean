import Analysis.Dilogarithm
import Analysis.AnalyticLinearODE

/-!
The normalized analytic J function from CDT v2, equations `newfunction`
and `odeJ` (supplied TeX lines 7374-7387). Its rational recurrence realizes
the regularized ODE on the open unit disk. See the mathematical note for
the separate hypergeometric and descent identification obligations.
-/

namespace DirichletL

open Filter
open scoped Topology NNReal ENNReal

/-- The rational Taylor coefficients of the normalized J equation. -/
noncomputable def pureJCoeff : ℕ → ℚ
  | 0 => 0
  | n + 1 => ((2 * (n : ℚ) - 1) * pureJCoeff n + 2 / ((n : ℚ) + 1) -
      2 / (n : ℚ)) / (2 * ((n : ℚ) + 1))

@[simp]
theorem pureJCoeff_zero : pureJCoeff 0 = 0 := rfl

theorem pureJCoeff_succ (n : ℕ) :
    pureJCoeff (n + 1) = ((2 * (n : ℚ) - 1) * pureJCoeff n +
      2 / ((n : ℚ) + 1) - 2 / (n : ℚ)) / (2 * ((n : ℚ) + 1)) := rfl

theorem pureJCoeff_recurrence (n : ℕ) :
    2 * ((n : ℚ) + 1) * pureJCoeff (n + 1) =
      (2 * (n : ℚ) - 1) * pureJCoeff n + 2 / ((n : ℚ) + 1) - 2 / (n : ℚ) := by
  rw [pureJCoeff_succ, ← mul_div_assoc, mul_div_cancel_left₀ _ (by positivity)]

theorem pureJCoeff_initial :
    pureJCoeff 1 = 1 ∧ pureJCoeff 2 = 0 ∧ pureJCoeff 3 = -1 / 18 := by
  norm_num [pureJCoeff]

theorem abs_pureJCoeff_le (n : ℕ) : |pureJCoeff n| ≤ 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rcases n with _ | n
    · norm_num [pureJCoeff]
    rw [pureJCoeff_succ]
    push_cast
    have hn : (1 : ℚ) ≤ (n : ℚ) + 1 := by linarith [Nat.cast_nonneg (α := ℚ) n]
    have ha : 0 ≤ 2 * ((n : ℚ) + 1) - 1 := by linarith
    rw [abs_div, abs_of_pos (by positivity : (0 : ℚ) < 2 * ((n + 1) + 1))]
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      _ ≤ |(2 * ((n : ℚ) + 1) - 1) * pureJCoeff (n + 1)| +
          |2 / ((n : ℚ) + 1 + 1)| + |2 / ((n : ℚ) + 1)| :=
        (abs_sub _ _).trans (add_le_add_right (abs_add_le _ _) _)
      _ = (2 * ((n : ℚ) + 1) - 1) * |pureJCoeff (n + 1)| +
          2 / ((n : ℚ) + 1 + 1) + 2 / ((n : ℚ) + 1) := by
        rw [abs_mul, abs_of_nonneg ha,
          abs_of_pos (by positivity : (0 : ℚ) < 2 / ((n : ℚ) + 1 + 1)),
          abs_of_pos (by positivity : (0 : ℚ) < 2 / ((n : ℚ) + 1))]
      _ ≤ (2 * ((n : ℚ) + 1) - 1) * 2 + 2 + 2 :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left ih ha)
          (div_le_self (by norm_num) (by linarith)))
          (div_le_self (by norm_num) hn)
      _ ≤ _ := by linarith

/-- The rational formal series of the normalized first-order J equation. -/
noncomputable def pureJSeries : PowerSeries ℚ := PowerSeries.mk pureJCoeff

@[simp]
theorem coeff_pureJSeries (n : ℕ) : PowerSeries.coeff (R := ℚ) n pureJSeries = pureJCoeff n :=
  PowerSeries.coeff_mk _ _

/-- The formal equation has a removable logarithmic quotient at the origin. -/
theorem pureJSeries_ode :
    PowerSeries.C (R := ℚ) 2 * ((PowerSeries.X - 1) * pureJSeries.derivativeFun) =
      pureJSeries + PowerSeries.C (R := ℚ) 2 *
        ((PowerSeries.X - 1) * formalShift pureLogarithmSeries) := by
  ext n
  rcases n with _ | n
  · simp only [sub_mul, one_mul, PowerSeries.coeff_C_mul, map_add, map_sub,
      PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_derivativeFun,
      coeff_pureJSeries, coeff_formalShift, coeff_pureLogarithmSeries]
    norm_num [pureJCoeff]
  · simp only [sub_mul, one_mul, map_add, PowerSeries.coeff_C_mul, map_sub,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivativeFun,
      coeff_pureJSeries, coeff_formalShift, coeff_pureLogarithmSeries]
    have h := pureJCoeff_recurrence (n + 1)
    push_cast at h ⊢
    linear_combination -h

theorem le_radius_complexSeries_pureJSeries :
    1 ≤ (complexSeries pureJSeries).radius := by
  apply (complexSeries pureJSeries).le_radius_of_bound (r := (1 : ℝ≥0)) 2
  intro n
  simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef, coeff_complexSeries,
    coeff_pureJSeries, Complex.norm_ratCast, NNReal.coe_one, one_pow, mul_one]
  exact_mod_cast abs_pureJCoeff_le n

/-- The exact convergent series with J(0)=0 for the source's first-order equation. -/
noncomputable def pureJ : ℂ → ℂ := (complexSeries pureJSeries).sum

theorem hasFPowerSeriesOnBall_pureJ :
    HasFPowerSeriesOnBall pureJ (complexSeries pureJSeries) 0 1 :=
  ((complexSeries pureJSeries).hasFPowerSeriesOnBall
    (lt_of_lt_of_le (by norm_num) le_radius_complexSeries_pureJSeries)).mono
    (by norm_num) le_radius_complexSeries_pureJSeries

private theorem mem_unit_ball {z : ℂ} (hz : ‖z‖ < 1) :
    z ∈ EMetric.ball 0 (1 : ℝ≥0∞) := by
  simpa only [EMetric.mem_ball, edist_zero_right, ← ofReal_norm_eq_enorm,
    ENNReal.ofReal_lt_one] using hz

theorem hasSum_pureJ {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => (pureJCoeff n : ℂ) * z ^ n) (pureJ z) := by
  simpa only [coeff_pureJSeries] using
    hasSum_of_hasFPowerSeriesOnBall hasFPowerSeriesOnBall_pureJ (mem_unit_ball hz)

theorem analyticAt_pureJ {z : ℂ} (hz : ‖z‖ < 1) : AnalyticAt ℂ pureJ z :=
  hasFPowerSeriesOnBall_pureJ.analyticAt_of_mem (mem_unit_ball hz)

@[simp]
theorem pureJ_zero : pureJ 0 = 0 := by
  change FormalMultilinearSeries.ofScalarsSum
    (fun n => (PowerSeries.coeff (R := ℚ) n pureJSeries : ℂ)) 0 = 0
  simp [FormalMultilinearSeries.ofScalarsSum_zero]

@[simp]
theorem deriv_pureJ_zero : deriv pureJ 0 = 1 := by
  simpa [coeff_complexSeries, pureJCoeff] using
    hasFPowerSeriesOnBall_pureJ.hasFPowerSeriesAt.deriv

theorem pureJ_regularized_ode {z : ℂ} (hz : ‖z‖ < 1) :
    2 * (z - 1) * deriv pureJ z = pureJ z +
      2 * (z - 1) * dslope (fun w : ℂ => -Complex.log (1 - w)) 0 z := by
  have h0 := hasSum_of_hasFPowerSeriesOnBall hasFPowerSeriesOnBall_pureJ (mem_unit_ball hz)
  have h1 := hasSum_of_hasFPowerSeriesOnBall
    (hasFPowerSeriesOnBall_derivativeFun hasFPowerSeriesOnBall_pureJ) (mem_unit_ball hz)
  have hb := hasSum_of_hasFPowerSeriesOnBall
    (hasFPowerSeriesOnBall_dslope hasFPowerSeriesOnBall_neg_clog_one_sub) (mem_unit_ball hz)
  have hl := (hasSum_polynomial_mul h1 (Polynomial.X - 1)).mul_left (2 : ℂ)
  have hr := h0.add ((hasSum_polynomial_mul hb (Polynomial.X - 1)).mul_left (2 : ℂ))
  have he (n : ℕ) := congrArg (fun p => (PowerSeries.coeff (R := ℚ) n p : ℂ)) pureJSeries_ode
  simp only [PowerSeries.coeff_C_mul, map_add, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_add] at he
  have heq : (fun n => 2 * ((PowerSeries.coeff (R := ℚ) n
      (((Polynomial.X - 1 : Polynomial ℚ) : PowerSeries ℚ) *
        pureJSeries.derivativeFun) : ℂ) * z ^ n)) =
      (fun n => (PowerSeries.coeff (R := ℚ) n pureJSeries : ℂ) * z ^ n +
        2 * ((PowerSeries.coeff (R := ℚ) n
          (((Polynomial.X - 1 : Polynomial ℚ) : PowerSeries ℚ) *
            formalShift pureLogarithmSeries) : ℂ) * z ^ n)) := by
    funext n
    simp only [Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_one]
    linear_combination he n * z ^ n
  rw [heq] at hl
  simpa [mul_assoc] using hl.unique hr

theorem hasDerivAt_pureJ {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt pureJ (pureJ z / (2 * (z - 1)) +
      dslope (fun w : ℂ => -Complex.log (1 - w)) 0 z) z := by
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (by intro h; simp [h] at hz)
  have he := pureJ_regularized_ode hz
  have hd : deriv pureJ z = pureJ z / (2 * (z - 1)) +
      dslope (fun w : ℂ => -Complex.log (1 - w)) 0 z := by
    apply mul_right_cancel₀ (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hz1)
    rw [add_mul, div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hz1)]
    linear_combination he
  rw [← hd]
  exact (analyticAt_pureJ hz).differentiableAt.hasDerivAt

theorem pureJ_ode {z : ℂ} (hz : ‖z‖ < 1) :
    2 * z * (z - 1) * deriv pureJ z - z * pureJ z =
      2 * (1 - z) * Complex.log (1 - z) := by
  by_cases hz0 : z = 0
  · simp [hz0]
  have he := pureJ_regularized_ode hz
  rw [dslope_of_ne _ hz0] at he
  simp [slope, smul_eq_mul, div_eq_mul_inv] at he
  field_simp [hz0] at he
  linear_combination he

/-- The regularized equation and zero initial value determine the analytic J germ. -/
theorem eventuallyEq_pureJ_of_ode {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hode : ∀ᶠ z in 𝓝 (0 : ℂ), HasDerivAt F
      (F z / (2 * (z - 1)) + dslope (fun w : ℂ => -Complex.log (1 - w)) 0 z) z) :
    F =ᶠ[𝓝 0] pureJ := by
  let A : ℂ → Matrix (Fin 1) (Fin 1) ℂ := fun z _ _ => 1 / (2 * (z - 1))
  have ha : AnalyticAt ℂ (fun z : ℂ => 1 / (2 * (z - 1))) 0 :=
    analyticAt_const.div (analyticAt_const.mul (analyticAt_id.sub analyticAt_const))
      (by norm_num)
  have hA : ContinuousAt A 0 :=
    continuousAt_pi.mpr (fun _ => continuousAt_pi.mpr (fun _ => ha.continuousAt))
  have hn : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < 1 :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by norm_num)
  have he := eventuallyEq_zero_of_analytic_matrix_ode (f := fun z (_ : Fin 1) => F z - pureJ z)
    hA (analyticAt_pi_iff.mpr (fun _ => hF.sub (analyticAt_pureJ (by norm_num))))
    (by ext i; simp [hF0]) (by
      filter_upwards [hode, hn] with z hz hzn
      apply hasDerivAt_pi.mpr
      intro i
      convert hz.sub (hasDerivAt_pureJ hzn) using 1
      simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_one, div_eq_mul_inv]
      ring)
  filter_upwards [he] with z hz
  exact sub_eq_zero.mp (congrFun hz (0 : Fin 1))

end DirichletL

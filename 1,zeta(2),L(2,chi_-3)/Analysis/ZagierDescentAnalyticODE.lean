import Analysis.ZagierDescentEquation
import Analysis.MobiusDescentAnalytic

/-!
Analytic realization of CDT v2 equation `explicitode` for the descended
Zagier function, and persistence of the equation under analytic continuation.
The continuation theorems take the analytic function as an explicit input.
-/

namespace DirichletL

open Filter
open scoped Topology ENNReal

/-- The analytic fourth-order residual from CDT v2 equation `explicitode`. -/
noncomputable def zagierAnalyticODE (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (zagierODECoeff 0).eval z * f z +
    (zagierODECoeff 1).eval z * deriv f z +
    (zagierODECoeff 2).eval z * deriv (deriv f) z +
    (zagierODECoeff 3).eval z * deriv (deriv (deriv f)) z +
    (zagierODECoeff 4).eval z * deriv (deriv (deriv (deriv f))) z

theorem aeval_zagierODECoeffQ (i : Fin 5) (z : ℂ) :
    Polynomial.aeval z (zagierODECoeffQ i) = (zagierODECoeff i).eval z := by
  rw [← map_zagierODECoeffQ, Polynomial.eval_map, Polynomial.aeval_def]

/-- A convergent formal solution satisfies the complex fourth-order equation. -/
theorem zagierAnalyticODE_eq_zero_of_hasFPowerSeriesOnBall {f : ℂ → ℂ}
    {p : PowerSeries ℚ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (complexSeries p) 0 r)
    (hp : zagierDescendedODE p = 0) {z : ℂ} (hz : z ∈ EMetric.ball 0 r) :
    zagierAnalyticODE f z = 0 := by
  have hf1 := hasFPowerSeriesOnBall_derivativeFun hf
  have hf2 := hasFPowerSeriesOnBall_derivativeFun hf1
  have hf3 := hasFPowerSeriesOnBall_derivativeFun hf2
  have hf4 := hasFPowerSeriesOnBall_derivativeFun hf3
  have h0 := hasSum_polynomial_mul (hasSum_of_hasFPowerSeriesOnBall hf hz)
    (zagierODECoeffQ 0)
  have h1 := hasSum_polynomial_mul (hasSum_of_hasFPowerSeriesOnBall hf1 hz)
    (zagierODECoeffQ 1)
  have h2 := hasSum_polynomial_mul (hasSum_of_hasFPowerSeriesOnBall hf2 hz)
    (zagierODECoeffQ 2)
  have h3 := hasSum_polynomial_mul (hasSum_of_hasFPowerSeriesOnBall hf3 hz)
    (zagierODECoeffQ 3)
  have h4 := hasSum_polynomial_mul (hasSum_of_hasFPowerSeriesOnBall hf4 hz)
    (zagierODECoeffQ 4)
  have hs : HasSum
      (fun n => (PowerSeries.coeff (R := ℚ) n (zagierDescendedODE p) : ℂ) * z ^ n)
      (zagierAnalyticODE f z) := by
    convert (((h0.add h1).add h2).add h3).add h4 using 1
    · ext n
      change (PowerSeries.coeff (R := ℚ) n
        ((zagierODECoeffQ 0 : PowerSeries ℚ) * p +
          (zagierODECoeffQ 1 : PowerSeries ℚ) * p.derivativeFun +
          (zagierODECoeffQ 2 : PowerSeries ℚ) * p.derivativeFun.derivativeFun +
          (zagierODECoeffQ 3 : PowerSeries ℚ) * p.derivativeFun.derivativeFun.derivativeFun +
          (zagierODECoeffQ 4 : PowerSeries ℚ) *
            p.derivativeFun.derivativeFun.derivativeFun.derivativeFun) : ℂ) * z ^ n = _
      simp only [map_add, Rat.cast_add, add_mul]
    · simp only [zagierAnalyticODE, aeval_zagierODECoeffQ]
  have hz0 (n : ℕ) : (PowerSeries.coeff (R := ℚ) n (zagierDescendedODE p) : ℂ) * z ^ n = 0 := by
    rw [hp, map_zero, Rat.cast_zero, zero_mul]
  exact hs.unique (by simpa only [hz0] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0))

/-- CDT's actual analytic `G_A` satisfies `explicitode` on its verified disk. -/
theorem zagierAnalyticODE_symmetrizedAnalytic_hA {z : ℂ} (hz : ‖z‖ < 1 / 648) :
    zagierAnalyticODE (symmetrizedAnalytic hA) z = 0 := by
  apply zagierAnalyticODE_eq_zero_of_hasFPowerSeriesOnBall
    hasFPowerSeriesOnBall_symmetrizedAnalytic_hA zagierDescendedODE_symmetrizedDescent_hA
  rw [EMetric.mem_ball, edist_zero_right, ← ofReal_norm_eq_enorm]
  have hr : ENNReal.ofReal (1 / 648 : ℝ) = (1 / 648 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  rw [← hr]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 648)).mpr hz

theorem eventuallyEq_zagierAnalyticODE_symmetrizedAnalytic_hA :
    zagierAnalyticODE (symmetrizedAnalytic hA) =ᶠ[𝓝 0] 0 := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 648)] with z hz
  exact zagierAnalyticODE_symmetrizedAnalytic_hA
    (by simpa only [Metric.mem_ball, dist_zero_right] using hz)

/-- The polynomial residual is analytic wherever the input function is analytic. -/
theorem analyticOnNhd_zagierAnalyticODE {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) : AnalyticOnNhd ℂ (zagierAnalyticODE f) U := by
  have hc (i : Fin 5) : AnalyticOnNhd ℂ (fun z => (zagierODECoeff i).eval z) U :=
    (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (zagierODECoeff i)).mono (Set.subset_univ U)
  exact ((((hc 0).mul hf).add ((hc 1).mul hf.deriv)).add
    ((hc 2).mul hf.deriv.deriv)).add ((hc 3).mul hf.deriv.deriv.deriv) |>.add
      ((hc 4).mul hf.deriv.deriv.deriv.deriv)

/-- Equality of germs implies equality of their polynomial ODE residuals. -/
theorem eventuallyEq_zagierAnalyticODE {f g : ℂ → ℂ} {z0 : ℂ}
    (h : f =ᶠ[𝓝 z0] g) : zagierAnalyticODE f =ᶠ[𝓝 z0] zagierAnalyticODE g := by
  filter_upwards [h, h.deriv, h.deriv.deriv, h.deriv.deriv.deriv,
    h.deriv.deriv.deriv.deriv] with z h0 h1 h2 h3 h4
  simp only [zagierAnalyticODE, h0, h1, h2, h3, h4]

/-- The analytic identity principle propagates the homogeneous equation. -/
theorem zagierAnalyticODE_eqOn_of_preconnected {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U) {z0 : ℂ} (hz0 : z0 ∈ U)
    (h0 : zagierAnalyticODE f =ᶠ[𝓝 z0] 0) : Set.EqOn (zagierAnalyticODE f) 0 U :=
  (analyticOnNhd_zagierAnalyticODE hf).eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hz0 h0

/-- Every supplied connected analytic continuation of the Zagier germ obeys its ODE. -/
theorem zagierAnalyticODE_eqOn_of_continuation_hA {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U) (h0 : (0 : ℂ) ∈ U)
    (hg : f =ᶠ[𝓝 0] symmetrizedAnalytic hA) : Set.EqOn (zagierAnalyticODE f) 0 U :=
  zagierAnalyticODE_eqOn_of_preconnected hf hU h0
    ((eventuallyEq_zagierAnalyticODE hg).trans
      eventuallyEq_zagierAnalyticODE_symmetrizedAnalytic_hA)

end DirichletL

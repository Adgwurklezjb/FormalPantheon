import Analysis.AnalyticLogIntegrability
import Analysis.CircleLogProfile

/-!
Boundary logarithmic profiles for CDT v2, supplied TeX 3505-3540 and 4150-4153.
-/

namespace DirichletL

theorem intervalIntegrable_circleLogProfile {ψ : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (Metric.closedBall 0 1)) :
    IntervalIntegrable (circleLogProfile ψ) MeasureTheory.volume 0 1 := by
  apply intervalIntegrable_log_norm_of_analyticOnNhd
  intro u _
  have hu : fourier 1 (u : AddCircle (1 : ℝ)) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq (Circle.norm_coe _)
  have hc : AnalyticAt ℝ (fun v : ℝ => fourier 1 (v : AddCircle (1 : ℝ))) u := by
    have he : AnalyticAt ℝ (fun v : ℝ => Complex.exp (2 * Real.pi * Complex.I * (v : ℂ))) u :=
      (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp'
        (analyticAt_const.mul (Complex.ofRealCLM.analyticAt u))
    simpa only [fourier_coe_apply, Int.cast_one, Complex.ofReal_one, mul_one, div_one] using he
  exact ((hψ _ hu).restrictScalars (𝕜 := ℝ)).comp'
    (f := fun v : ℝ => fourier 1 (v : AddCircle (1 : ℝ))) hc

end DirichletL

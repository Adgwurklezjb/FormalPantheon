import Analysis.AnalyticPrimitivesOnBalls

/-!
Analytic square roots with a specified value on a complex ball.
Source: CDT v2 TeX 7157-7173. Prior meaning and branch checks:
-/

namespace DirichletL

open scoped Topology

theorem exists_analytic_square_root_on_ball {f : ℂ → ℂ} {c s : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (Metric.ball c R))
    (hne : ∀ z ∈ Metric.ball c R, f z ≠ 0) (hs : s ^ 2 = f c) :
    ∃ S : ℂ → ℂ, AnalyticOnNhd ℂ S (Metric.ball c R) ∧ S c = s ∧
      ∀ z ∈ Metric.ball c R, S z ^ 2 = f z := by
  have hlog : AnalyticOnNhd ℂ (fun z => deriv f z / f z) (Metric.ball c R) :=
    fun z hz => (hf z hz).deriv.div (hf z hz) (hne z hz)
  obtain ⟨P, hPa, hP₀, hPd⟩ := exists_analytic_primitive_on_ball hR hlog
  have hzero (z : ℂ) (hz : z ∈ Metric.ball c R) :
      HasDerivAt (fun w => f w * Complex.exp (-P w)) 0 z := by
    convert ((hf z hz).differentiableAt.hasDerivAt).mul ((hPd z hz).neg.cexp) using 1
    field_simp [hne z hz]
    ring
  have hconstant (z : ℂ) (hz : z ∈ Metric.ball c R) :
      f z * Complex.exp (-P z) = f c := by
    have h := Metric.isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball c R).isPreconnected
      (fun w hw => (hzero w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hzero w hw).deriv) hz (Metric.mem_ball_self hR)
    simpa only [hP₀, neg_zero, Complex.exp_zero, mul_one] using h
  have hreconstruct (z : ℂ) (hz : z ∈ Metric.ball c R) :
      f z = f c * Complex.exp (P z) := by
    have h := congrArg (fun w => w * Complex.exp (P z)) (hconstant z hz)
    simpa only [mul_assoc, ← Complex.exp_add, neg_add_cancel,
      Complex.exp_zero, mul_one] using h
  refine ⟨fun z => s * Complex.exp (P z / 2),
    fun z hz => analyticAt_const.mul
      ((hPa z hz).div analyticAt_const (by norm_num : (2 : ℂ) ≠ 0)).cexp, ?_, ?_⟩
  · simp [hP₀]
  · intro z hz
    have hexp : Complex.exp (P z / 2) ^ 2 = Complex.exp (P z) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
    rw [mul_pow, hs, hexp, ← hreconstruct z hz]

end DirichletL

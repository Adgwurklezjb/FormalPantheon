import Analysis.ComplexLogarithmBranches

/-!
The standard circle path and its continuous exponential lift, for the local
logarithmic continuation in CDT v2 equation `zagr`.
-/

namespace DirichletL

open unitInterval
open scoped Topology

/-- The standard circle, traversed once on the closed unit interval. -/
noncomputable def complexCirclePath (r : ℝ) : Path (r : ℂ) (r : ℂ) where
  toFun t := circleMap 0 r (2 * Real.pi * (t : ℝ))
  continuous_toFun := (continuous_circleMap 0 r).comp (by fun_prop)
  source' := by simp [circleMap]
  target' := by simp [circleMap, Complex.exp_two_pi_mul_I]

@[simp] theorem complexCirclePath_apply (r : ℝ) (t : I) :
    complexCirclePath r t = circleMap 0 r (2 * Real.pi * (t : ℝ)) := rfl

theorem norm_complexCirclePath (r : ℝ) (t : I) :
    ‖complexCirclePath r t‖ = |r| := by
  rw [complexCirclePath_apply, norm_circleMap_zero]

theorem complexCirclePath_ne_one {r : ℝ} (hr : |r| < 1) (t : I) :
    complexCirclePath r t ≠ 1 := by
  intro he
  have h := norm_complexCirclePath r t
  rw [he, norm_one] at h
  linarith

/-- A continuous lift of the circle parameter to the exponential coordinate. -/
noncomputable def complexCircleLift (r : ℝ) (t : I) : ℂ :=
  Complex.log (r : ℂ) + (2 * Real.pi * (t : ℝ) : ℝ) * Complex.I

@[simp] theorem complexCircleLift_zero (r : ℝ) : complexCircleLift r 0 = Complex.log r := by
  simp [complexCircleLift]

@[simp] theorem complexCircleLift_one (r : ℝ) :
    complexCircleLift r 1 = Complex.log r + 2 * Real.pi * Complex.I := by
  simp [complexCircleLift]

theorem continuous_complexCircleLift (r : ℝ) : Continuous (complexCircleLift r) := by
  unfold complexCircleLift
  fun_prop

theorem exp_complexCircleLift {r : ℝ} (hr : 0 < r) (t : I) :
    Complex.exp (complexCircleLift r t) = complexCirclePath r t := by
  have hr₀ : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [complexCircleLift, Complex.exp_add, Complex.exp_log hr₀, complexCirclePath_apply,
    circleMap_zero]

end DirichletL

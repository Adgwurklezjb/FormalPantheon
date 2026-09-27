import Analysis.ContourDiskMap

/-!
Whole angular cells for the corrected CDT contour, author revision A.4, page 204.
Meanings and angle conventions precede these bodies in
-/

namespace DirichletL

theorem contourRotation_eq_fourier (θ : ℝ) :
    contourRotation θ = fourier 1 (θ : AddCircle (1 : ℝ)) := by
  rw [fourier_coe_apply]
  unfold contourRotation
  congr 1
  push_cast
  ring

theorem contourRotation_add_int (θ : ℝ) (k : ℤ) :
    contourRotation (θ + (k : ℝ)) = contourRotation θ := by
  have heq : (((2 * Real.pi * (θ + (k : ℝ)) : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I) +
        (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  simp only [contourRotation, heq, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem norm_contourRotation_sub_le (θ φ : ℝ) :
    ‖contourRotation θ - contourRotation φ‖ ≤ 2 * Real.pi * |θ - φ| := by
  have h : ‖contourRotation θ - contourRotation φ‖ ≤
      |2 * Real.pi * θ - 2 * Real.pi * φ| := by
    simpa [circleMap, contourRotation, dist_eq_norm, Real.norm_eq_abs, Real.coe_nnabs] using
      (lipschitzWith_circleMap (0 : ℂ) 1).dist_le_mul
        (2 * Real.pi * θ) (2 * Real.pi * φ)
  have heq : 2 * Real.pi * θ - 2 * Real.pi * φ = 2 * Real.pi * (θ - φ) := by ring
  simpa only [heq, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] using h

theorem norm_radius_contourRotation_sub_midpoint_le {r l u x : ℝ}
    (hx : x ∈ Set.Icc l u) :
    ‖(r : ℂ) * contourRotation x -
      (r : ℂ) * contourRotation ((l + u) / 2)‖ ≤ |r| * Real.pi * (u - l) := by
  have hm : |x - (l + u) / 2| ≤ (u - l) / 2 := by
    apply abs_le.mpr
    constructor <;> linarith only [hx.1, hx.2]
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |r| * (2 * Real.pi * |x - (l + u) / 2|) :=
      mul_le_mul_of_nonneg_left (norm_contourRotation_sub_le _ _) (abs_nonneg r)
    _ ≤ |r| * (2 * Real.pi * ((u - l) / 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hm (by positivity)) (abs_nonneg r)
    _ = _ := by ring

end DirichletL

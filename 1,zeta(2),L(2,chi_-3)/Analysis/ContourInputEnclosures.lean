import Analysis.ScaledRectangleExp
import Analysis.ContourDiskMap

/-!
Certified inputs for CDT's corrected rotations and two-radius contour, author revision
Appendix A.4, page 204, and page 174. Meanings and exact constant checks precede
-/

namespace DirichletL.ScaledRectangle

/-- Enclose pi using Mathlib's exact bounds with twenty digits after the decimal point. -/
def piInterval (D : ℕ) : NonemptyInterval ℤ :=
  ScaledInterval.rational D 314159265358979323846 (10 ^ 20) ⊔
    ScaledInterval.rational D 314159265358979323847 (10 ^ 20)

theorem pi_mem {D : ℕ} (hD : 0 < D) :
    Real.pi ∈ ScaledInterval.denote D (piInterval D) := by
  have hl : (314159265358979323846 : ℝ) / 10 ^ 20 ∈ ScaledInterval.denote D
      (ScaledInterval.rational D 314159265358979323846 (10 ^ 20)) := by
    convert ScaledInterval.rational_mem hD 314159265358979323846 (10 ^ 20)
      (by norm_num) using 1
    norm_num
  have hu : (314159265358979323847 : ℝ) / 10 ^ 20 ∈ ScaledInterval.denote D
      (ScaledInterval.rational D 314159265358979323847 (10 ^ 20)) := by
    convert ScaledInterval.rational_mem hD 314159265358979323847 (10 ^ 20)
      (by norm_num) using 1
    norm_num
  have hpl : (314159265358979323846 : ℝ) / 10 ^ 20 ≤ Real.pi := by
    convert Real.pi_gt_d20.le using 1
    norm_num
  have hpu : Real.pi ≤ (314159265358979323847 : ℝ) / 10 ^ 20 := by
    convert Real.pi_lt_d20.le using 1
    norm_num
  rw [ScaledInterval.mem_denote_iff hD] at hl hu ⊢
  simp only [piInterval, NonemptyInterval.fst_sup, NonemptyInterval.snd_sup,
    Int.cast_min, Int.cast_max]
  exact ⟨(min_le_left _ _).trans (hl.1.trans
      (mul_le_mul_of_nonneg_left hpl (Nat.cast_nonneg D))),
    ((mul_le_mul_of_nonneg_left hpu (Nat.cast_nonneg D)).trans hu.2).trans
      (le_max_right _ _)⟩

/-- A rational number of turns, evaluated by the fixed exponential enclosure. -/
def rotation (D : ℕ) (n d : ℤ) : ScaledRectangle :=
  exp48 D (0, ScaledInterval.mul D (ScaledInterval.rational D (2 * n) d) (piInterval D))

theorem rotation_mem {D : ℕ} (hD : 0 < D) (n d : ℤ) (hd : 0 < d)
    (ht : |(n : ℝ) / (d : ℝ)| ≤ 1 / 2) :
    contourRotation ((n : ℝ) / (d : ℝ)) ∈ denote D (rotation D n d) := by
  have hz : (((2 * Real.pi * ((n : ℝ) / (d : ℝ)) : ℝ) : ℂ) * Complex.I) ∈
      denote D (0, ScaledInterval.mul D (ScaledInterval.rational D (2 * n) d)
        (piInterval D)) := by
    constructor
    · simp [ScaledInterval.denote]
    · have ha := ScaledInterval.mul_mem hD (ScaledInterval.rational_mem hD (2 * n) d hd)
        (pi_mem hD)
      convert ha using 1
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_one, zero_mul, add_zero, Int.cast_mul, Int.cast_ofNat]
      ring
  have hn : ‖((2 * Real.pi * ((n : ℝ) / (d : ℝ)) : ℝ) : ℂ) * Complex.I‖ ≤ 4 := by
    calc
      _ = 2 * Real.pi * |(n : ℝ) / (d : ℝ)| := by
        simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
          abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ Real.pi := by nlinarith [mul_le_mul_of_nonneg_left ht Real.pi_pos.le]
      _ ≤ 4 := Real.pi_lt_four.le
  exact exp48_mem hD hz hn

/-- The real component of the exponential enclosure for the inner radius. -/
def innerRadius (D : ℕ) : NonemptyInterval ℤ := (exp48 D (rational D (-1) 2)).1

theorem innerRadius_mem {D : ℕ} (hD : 0 < D) :
    Real.exp (-1 / 2) ∈ ScaledInterval.denote D (innerRadius D) := by
  have hz : ((-1 / 2 : ℝ) : ℂ) ∈ denote D (rational D (-1) 2) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one,
      Complex.ofReal_ofNat, Int.cast_neg, Int.cast_one, Int.cast_ofNat] using
      rational_mem hD (-1) 2 (by norm_num)
  simpa only [Complex.exp_ofReal_re] using (exp48_mem hD hz (by norm_num)).1

end DirichletL.ScaledRectangle

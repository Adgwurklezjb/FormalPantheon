import Analysis.ScaledRectangleNorm
import Analysis.ComplexSquareRootComponents

/-!
Principal-root enclosures for CDT's corrected contour, author revision A.4, page 204.
-/

namespace DirichletL.ScaledRectangle

/-- Enclose the nonnegative real part of the principal square root. -/
def sqrtRe (D : ℕ) (Z : ScaledRectangle) : NonemptyInterval ℤ :=
  ScaledInterval.sqrt D (ScaledInterval.mul D (ScaledInterval.rational D 1 2)
    (norm D Z + Z.1))

theorem sqrtRe_mem {D : ℕ} (hD : 0 < D) {Z : ScaledRectangle} {z : ℂ}
    (hz : z ∈ denote D Z) :
    (z ^ (2⁻¹ : ℂ)).re ∈ ScaledInterval.denote D (sqrtRe D Z) := by
  have hp : 0 ≤ ‖z‖ + z.re := by
    linarith [Complex.abs_re_le_norm z, neg_le_abs z.re]
  have hm : (‖z‖ + z.re) / 2 ∈ ScaledInterval.denote D
      (ScaledInterval.mul D (ScaledInterval.rational D 1 2) (norm D Z + Z.1)) := by
    convert ScaledInterval.mul_mem hD (ScaledInterval.rational_mem hD 1 2 (by norm_num))
      (ScaledInterval.add_mem hD (norm_mem hD hz) hz.1) using 1
    push_cast
    ring
  simpa only [Complex.cpow_inv_two_re] using
    ScaledInterval.sqrt_mem hD (div_nonneg hp (by norm_num)) hm

/-- Enclose the absolute imaginary part of the principal square root. -/
def sqrtImAbs (D : ℕ) (Z : ScaledRectangle) : NonemptyInterval ℤ :=
  ScaledInterval.sqrt D (ScaledInterval.mul D (ScaledInterval.rational D 1 2)
    (norm D Z - Z.1))

theorem sqrtImAbs_mem {D : ℕ} (hD : 0 < D) {Z : ScaledRectangle} {z : ℂ}
    (hz : z ∈ denote D Z) :
    |(z ^ (2⁻¹ : ℂ)).im| ∈ ScaledInterval.denote D (sqrtImAbs D Z) := by
  have hm : (‖z‖ - z.re) / 2 ∈ ScaledInterval.denote D
      (ScaledInterval.mul D (ScaledInterval.rational D 1 2) (norm D Z - Z.1)) := by
    convert ScaledInterval.mul_mem hD (ScaledInterval.rational_mem hD 1 2 (by norm_num))
      (ScaledInterval.sub_mem hD (norm_mem hD hz) hz.1) using 1
    push_cast
    ring
  simpa only [Complex.abs_cpow_inv_two_im] using
    ScaledInterval.sqrt_mem hD (div_nonneg (sub_nonneg.mpr (Complex.re_le_norm z))
      (by norm_num)) hm

/-- Recover the imaginary coordinate from a positive lower real-root bound. -/
def sqrtOfRe (D : ℕ) (Z : ScaledRectangle) : ScaledRectangle :=
  (sqrtRe D Z, ScaledInterval.mul D (ScaledInterval.rational D 1 2)
    (ScaledInterval.mul D Z.2 (ScaledInterval.inv D (sqrtRe D Z))))

theorem sqrtOfRe_mem {D : ℕ} (hD : 0 < D) {Z : ScaledRectangle} {z : ℂ}
    (hR : 0 < (sqrtRe D Z).fst) (hz : z ∈ denote D Z) :
    z ^ (2⁻¹ : ℂ) ∈ denote D (sqrtOfRe D Z) := by
  have hr := sqrtRe_mem hD hz
  have hp : 0 < (z ^ (2⁻¹ : ℂ)).re := by
    apply (mul_pos_iff_of_pos_left (show (0 : ℝ) < D by exact_mod_cast hD)).1
    exact (show (0 : ℝ) < (sqrtRe D Z).fst by exact_mod_cast hR).trans_le
      ((ScaledInterval.mem_denote_iff hD).mp hr).1
  refine ⟨hr, ?_⟩
  rw [im_cpow_inv_two_eq_div hp.ne']
  convert ScaledInterval.mul_mem hD (ScaledInterval.rational_mem hD 1 2 (by norm_num))
    (ScaledInterval.mul_mem hD hz.2 (ScaledInterval.inv_mem hD hR hr)) using 1
  push_cast
  field_simp

/-- Recover the real coordinate from a positive imaginary-root bound. -/
def sqrtOfNonnegIm (D : ℕ) (Z : ScaledRectangle) : ScaledRectangle :=
  (ScaledInterval.mul D (ScaledInterval.rational D 1 2)
    (ScaledInterval.mul D Z.2 (ScaledInterval.inv D (sqrtImAbs D Z))), sqrtImAbs D Z)

theorem sqrtOfNonnegIm_mem {D : ℕ} (hD : 0 < D) {Z : ScaledRectangle} {z : ℂ}
    (hB : 0 < (sqrtImAbs D Z).fst) (hZ : 0 ≤ Z.2.fst) (hz : z ∈ denote D Z) :
    z ^ (2⁻¹ : ℂ) ∈ denote D (sqrtOfNonnegIm D Z) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hz0 : 0 ≤ z.im := by
    apply (mul_nonneg_iff_of_pos_left hDr).1
    exact (show (0 : ℝ) ≤ Z.2.fst by exact_mod_cast hZ).trans
      ((ScaledInterval.mem_denote_iff hD).mp hz.2).1
  have hs : 0 ≤ (z ^ (2⁻¹ : ℂ)).im := by
    rw [Complex.cpow_inv_two_im_eq_sqrt hz0]
    exact Real.sqrt_nonneg _
  have hb := sqrtImAbs_mem hD hz
  rw [abs_of_nonneg hs] at hb
  have hp : 0 < (z ^ (2⁻¹ : ℂ)).im := by
    apply (mul_pos_iff_of_pos_left hDr).1
    exact (show (0 : ℝ) < (sqrtImAbs D Z).fst by exact_mod_cast hB).trans_le
      ((ScaledInterval.mem_denote_iff hD).mp hb).1
  refine ⟨?_, hb⟩
  rw [re_cpow_inv_two_eq_div hp.ne']
  convert ScaledInterval.mul_mem hD (ScaledInterval.rational_mem hD 1 2 (by norm_num))
    (ScaledInterval.mul_mem hD hz.2 (ScaledInterval.inv_mem hD hB hb)) using 1
  push_cast
  field_simp

/-- Use a positive absolute imaginary-root bound on the lower half-plane. -/
def sqrtOfNegIm (D : ℕ) (Z : ScaledRectangle) : ScaledRectangle :=
  (ScaledInterval.mul D (ScaledInterval.rational D 1 2)
    (ScaledInterval.mul D (-Z.2) (ScaledInterval.inv D (sqrtImAbs D Z))), -sqrtImAbs D Z)

theorem sqrtOfNegIm_mem {D : ℕ} (hD : 0 < D) {Z : ScaledRectangle} {z : ℂ}
    (hB : 0 < (sqrtImAbs D Z).fst) (hZ : Z.2.snd < 0) (hz : z ∈ denote D Z) :
    z ^ (2⁻¹ : ℂ) ∈ denote D (sqrtOfNegIm D Z) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hz0 : z.im < 0 := by
    have hp := ((ScaledInterval.mem_denote_iff hD).mp hz.2).2.trans_lt
      (show (Z.2.snd : ℝ) < 0 by exact_mod_cast hZ)
    by_contra hn
    exact (not_lt_of_ge (mul_nonneg hDr.le (le_of_not_gt hn))) hp
  have hs : (z ^ (2⁻¹ : ℂ)).im ≤ 0 := by
    rw [Complex.cpow_inv_two_im_eq_neg_sqrt hz0]
    exact neg_nonpos.mpr (Real.sqrt_nonneg _)
  have hb := sqrtImAbs_mem hD hz
  rw [abs_of_nonpos hs] at hb
  have hp : 0 < -(z ^ (2⁻¹ : ℂ)).im := by
    apply (mul_pos_iff_of_pos_left hDr).1
    exact (show (0 : ℝ) < (sqrtImAbs D Z).fst by exact_mod_cast hB).trans_le
      ((ScaledInterval.mem_denote_iff hD).mp hb).1
  constructor
  · rw [re_cpow_inv_two_eq_div (by linarith)]
    convert ScaledInterval.mul_mem hD (ScaledInterval.rational_mem hD 1 2 (by norm_num))
      (ScaledInterval.mul_mem hD (ScaledInterval.neg_mem hD hz.2)
        (ScaledInterval.inv_mem hD hB hb)) using 1
    push_cast
    field_simp
  · simpa only [neg_neg] using ScaledInterval.neg_mem hD hb

end DirichletL.ScaledRectangle

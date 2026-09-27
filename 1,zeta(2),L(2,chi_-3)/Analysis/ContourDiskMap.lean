import Analysis.ContourSlit
import Analysis.ContourLune

/-!
CDT author revision of 2026-09-02, Appendix A.4, page 204.
The corrected angle order and all meanings precede these revised bodies in
-/

namespace DirichletL

/-- The unit complex phase of an angle measured in turns. -/
noncomputable def contourRotation (theta : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * theta : ℝ) : ℂ) * Complex.I)

theorem norm_contourRotation (theta : ℝ) : ‖contourRotation theta‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- CDT's shrunken slit and lune composition, with the corrected author angle order. -/
noncomputable def cdtContourDiskMap (z : ℂ) : ℂ :=
  let z1 := contourSlitMap (91 / 100) ((995 / 1000 : ℂ) * z)
  let z2 := contourSlitMap (6188 / 10000) (contourRotation (7977 / 100000) * z1)
  let z3 := contourSlitMap (55515 / 100000) (contourRotation (11543 / 100000) * z2)
  let z4 := contourSlitMap (772 / 1000) (contourRotation (3525 / 100000) * z3)
  (-(77 / 100 : ℂ)) * contourLuneMap (75 / 10) (-contourRotation (-783 / 10000) * z4)

theorem cdtContourDiskMap_zero : cdtContourDiskMap 0 = 0 := by
  simp only [cdtContourDiskMap, mul_zero, contourSlitMap_zero, contourLuneMap_zero]

theorem norm_cdtContourDiskMap_lt {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖cdtContourDiskMap z‖ < (77 / 100 : ℝ) := by
  have h0 : ‖(995 / 1000 : ℂ) * z‖ < 1 := by
    rw [norm_mul]
    norm_num
    nlinarith only [hz]
  have h1 := norm_contourSlitMap_lt_one (by norm_num : (0 : ℝ) < 91 / 100)
    (by norm_num) h0
  have h2 := norm_contourSlitMap_lt_one (by norm_num : (0 : ℝ) < 6188 / 10000)
    (by norm_num) (by simpa only [norm_mul, norm_contourRotation, one_mul] using h1 :
      ‖contourRotation (7977 / 100000) * contourSlitMap (91 / 100)
        ((995 / 1000 : ℂ) * z)‖ < 1)
  have h3 := norm_contourSlitMap_lt_one (by norm_num : (0 : ℝ) < 55515 / 100000)
    (by norm_num) (by simpa only [norm_mul, norm_contourRotation, one_mul] using h2 :
      ‖contourRotation (11543 / 100000) * contourSlitMap (6188 / 10000)
        (contourRotation (7977 / 100000) * contourSlitMap (91 / 100)
          ((995 / 1000 : ℂ) * z))‖ < 1)
  have h4 := norm_contourSlitMap_lt_one (by norm_num : (0 : ℝ) < 772 / 1000)
    (by norm_num) (by simpa only [norm_mul, norm_contourRotation, one_mul] using h3 :
      ‖contourRotation (3525 / 100000) * contourSlitMap (55515 / 100000)
        (contourRotation (11543 / 100000) * contourSlitMap (6188 / 10000)
          (contourRotation (7977 / 100000) * contourSlitMap (91 / 100)
            ((995 / 1000 : ℂ) * z)))‖ < 1)
  have hL := norm_contourLuneMap_lt_one (by norm_num : (1 : ℝ) < 75 / 10)
    (by simpa only [norm_mul, norm_neg, norm_contourRotation, one_mul] using h4 :
      ‖-contourRotation (-783 / 10000) * contourSlitMap (772 / 1000)
        (contourRotation (3525 / 100000) * contourSlitMap (55515 / 100000)
          (contourRotation (11543 / 100000) * contourSlitMap (6188 / 10000)
            (contourRotation (7977 / 100000) * contourSlitMap (91 / 100)
              ((995 / 1000 : ℂ) * z))))‖ < 1)
  dsimp only [cdtContourDiskMap]
  rw [norm_mul, norm_neg]
  norm_num at hL ⊢
  exact hL

theorem analyticOnNhd_cdtContourDiskMap :
    AnalyticOnNhd ℂ cdtContourDiskMap (Metric.closedBall 0 1) := by
  intro z hz
  have hz1 : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  let f0 (w : ℂ) := (995 / 1000 : ℂ) * w
  let f1 (w : ℂ) := contourSlitMap (91 / 100) (f0 w)
  let f2 (w : ℂ) := contourSlitMap (6188 / 10000) (contourRotation (7977 / 100000) * f1 w)
  let f3 (w : ℂ) := contourSlitMap (55515 / 100000) (contourRotation (11543 / 100000) * f2 w)
  let f4 (w : ℂ) := contourSlitMap (772 / 1000) (contourRotation (3525 / 100000) * f3 w)
  have h0 : ‖f0 z‖ < 1 := by
    dsimp only [f0]
    rw [norm_mul]
    norm_num
    nlinarith only [hz1]
  have a0 : AnalyticAt ℂ f0 z := analyticAt_const.mul analyticAt_id
  have a1 : AnalyticAt ℂ f1 z :=
    (analyticAt_contourSlitMap (r := 91 / 100) (by norm_num) (by norm_num) h0).comp'
      (f := f0) a0
  have h1 : ‖f1 z‖ < 1 := norm_contourSlitMap_lt_one (r := 91 / 100) (by norm_num) (by norm_num) h0
  have h1r : ‖contourRotation (7977 / 100000) * f1 z‖ < 1 := by
    simpa only [norm_mul, norm_contourRotation, one_mul] using h1
  have a2 : AnalyticAt ℂ f2 z :=
    (analyticAt_contourSlitMap (r := 6188 / 10000) (by norm_num) (by norm_num) h1r).comp'
      (f := fun w => contourRotation (7977 / 100000) * f1 w) (analyticAt_const.mul a1)
  have h2 : ‖f2 z‖ < 1 := norm_contourSlitMap_lt_one (r := 6188 / 10000) (by norm_num) (by norm_num) h1r
  have h2r : ‖contourRotation (11543 / 100000) * f2 z‖ < 1 := by
    simpa only [norm_mul, norm_contourRotation, one_mul] using h2
  have a3 : AnalyticAt ℂ f3 z :=
    (analyticAt_contourSlitMap (r := 55515 / 100000) (by norm_num) (by norm_num) h2r).comp'
      (f := fun w => contourRotation (11543 / 100000) * f2 w) (analyticAt_const.mul a2)
  have h3 : ‖f3 z‖ < 1 := norm_contourSlitMap_lt_one (r := 55515 / 100000) (by norm_num) (by norm_num) h2r
  have h3r : ‖contourRotation (3525 / 100000) * f3 z‖ < 1 := by
    simpa only [norm_mul, norm_contourRotation, one_mul] using h3
  have a4 : AnalyticAt ℂ f4 z :=
    (analyticAt_contourSlitMap (r := 772 / 1000) (by norm_num) (by norm_num) h3r).comp'
      (f := fun w => contourRotation (3525 / 100000) * f3 w) (analyticAt_const.mul a3)
  have h4 : ‖f4 z‖ < 1 := norm_contourSlitMap_lt_one (r := 772 / 1000) (by norm_num) (by norm_num) h3r
  have h4r : ‖-contourRotation (-783 / 10000) * f4 z‖ < 1 := by
    simpa only [norm_mul, norm_neg, norm_contourRotation, one_mul] using h4
  exact analyticAt_const.mul ((analyticAt_contourLuneMap (c := 75 / 10) (by norm_num) h4r).comp'
    (f := fun w => -contourRotation (-783 / 10000) * f4 w) (analyticAt_const.mul a4))

theorem norm_deriv_cdtContourDiskMap_zero :
    ‖deriv cdtContourDiskMap 0‖ = cdtContourConformalRadius := by
  let f0 (w : ℂ) := (995 / 1000 : ℂ) * w
  let f1 (w : ℂ) := contourSlitMap (91 / 100) (f0 w)
  let f2 (w : ℂ) := contourSlitMap (6188 / 10000) (contourRotation (7977 / 100000) * f1 w)
  let f3 (w : ℂ) := contourSlitMap (55515 / 100000) (contourRotation (11543 / 100000) * f2 w)
  let f4 (w : ℂ) := contourSlitMap (772 / 1000) (contourRotation (3525 / 100000) * f3 w)
  have h0 : HasDerivAt f0 (995 / 1000) 0 := by
    simpa only [mul_one] using (hasDerivAt_id (𝕜 := ℂ) 0).const_mul (995 / 1000)
  have h10 : f0 0 = 0 := by simp [f0]
  have h20 : contourRotation (7977 / 100000) * f1 0 = 0 := by
    simp only [f1, h10, contourSlitMap_zero, mul_zero]
  have h30 : contourRotation (11543 / 100000) * f2 0 = 0 := by
    simp only [f2, h20, contourSlitMap_zero, mul_zero]
  have h40 : contourRotation (3525 / 100000) * f3 0 = 0 := by
    simp only [f3, h30, contourSlitMap_zero, mul_zero]
  have h50 : -contourRotation (-783 / 10000) * f4 0 = 0 := by
    simp only [f4, h40, contourSlitMap_zero, mul_zero]
  have h1 := (show HasDerivAt (contourSlitMap (91 / 100))
      ((4 * (91 / 100) / (1 + 91 / 100) ^ 2 : ℝ) : ℂ) (f0 0) by
    rw [h10]; exact hasDerivAt_contourSlitMap_zero _).comp 0 h0
  change HasDerivAt f1 _ 0 at h1
  have h2 := (show HasDerivAt (contourSlitMap (6188 / 10000))
      ((4 * (6188 / 10000) / (1 + 6188 / 10000) ^ 2 : ℝ) : ℂ)
      (contourRotation (7977 / 100000) * f1 0) by
    rw [h20]; exact hasDerivAt_contourSlitMap_zero _).comp 0
      (h1.const_mul (contourRotation (7977 / 100000)))
  change HasDerivAt f2 _ 0 at h2
  have h3 := (show HasDerivAt (contourSlitMap (55515 / 100000))
      ((4 * (55515 / 100000) / (1 + 55515 / 100000) ^ 2 : ℝ) : ℂ)
      (contourRotation (11543 / 100000) * f2 0) by
    rw [h30]; exact hasDerivAt_contourSlitMap_zero _).comp 0
      (h2.const_mul (contourRotation (11543 / 100000)))
  change HasDerivAt f3 _ 0 at h3
  have h4 := (show HasDerivAt (contourSlitMap (772 / 1000))
      ((4 * (772 / 1000) / (1 + 772 / 1000) ^ 2 : ℝ) : ℂ)
      (contourRotation (3525 / 100000) * f3 0) by
    rw [h40]; exact hasDerivAt_contourSlitMap_zero _).comp 0
      (h3.const_mul (contourRotation (3525 / 100000)))
  change HasDerivAt f4 _ 0 at h4
  have h5 := (show HasDerivAt (contourLuneMap (75 / 10))
      ((((75 / 10 : ℝ) ^ 2 - 1) / ((75 / 10 : ℝ) ^ 2 + 1) : ℝ) : ℂ)
      (-contourRotation (-783 / 10000) * f4 0) by
    rw [h50]; exact hasDerivAt_contourLuneMap_zero (c := 75 / 10) (by norm_num)).comp 0
      (h4.const_mul (-contourRotation (-783 / 10000)))
  have hG := h5.const_mul (-(77 / 100 : ℂ))
  change HasDerivAt cdtContourDiskMap _ 0 at hG
  rw [hG.deriv]
  simp only [norm_mul, norm_neg, norm_contourRotation, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  norm_num [cdtContourConformalRadius, abs_div]

theorem injOn_cdtContourDiskMap :
    Set.InjOn cdtContourDiskMap (Metric.closedBall (0 : ℂ) 1) := by
  let D := Metric.ball (0 : ℂ) 1
  let E := Metric.closedBall (0 : ℂ) 1
  have hstep (r theta : ℝ) (hr : 0 < r) (hr1 : r < 1) (f : ℂ → ℂ)
      (hm : Set.MapsTo f E D) (hi : Set.InjOn f E) :
      Set.MapsTo (fun z => contourSlitMap r (contourRotation theta * f z)) E D ∧
      Set.InjOn (fun z => contourSlitMap r (contourRotation theta * f z)) E := by
    have hrot {z : ℂ} (hz : z ∈ E) : contourRotation theta * f z ∈ D := by
      have h := hm hz
      simpa only [D, Metric.mem_ball, dist_zero_right, norm_mul, norm_contourRotation,
        one_mul] using h
    refine ⟨?_, ?_⟩
    · intro z hz
      simpa only [D, Metric.mem_ball, dist_zero_right] using
        norm_contourSlitMap_lt_one hr hr1 (by
          simpa only [D, Metric.mem_ball, dist_zero_right] using hrot hz)
    · intro z hz w hw he
      apply hi hz hw
      have hunit : contourRotation theta ≠ 0 :=
        norm_ne_zero_iff.mp (by rw [norm_contourRotation]; norm_num)
      exact mul_left_cancel₀ hunit (injOn_contourSlitMap hr hr1 (hrot hz) (hrot hw) he)
  let f0 (w : ℂ) := (995 / 1000 : ℂ) * w
  let f1 (w : ℂ) := contourSlitMap (91 / 100) (f0 w)
  let f2 (w : ℂ) := contourSlitMap (6188 / 10000) (contourRotation (7977 / 100000) * f1 w)
  let f3 (w : ℂ) := contourSlitMap (55515 / 100000) (contourRotation (11543 / 100000) * f2 w)
  let f4 (w : ℂ) := contourSlitMap (772 / 1000) (contourRotation (3525 / 100000) * f3 w)
  have hm0 : Set.MapsTo f0 E D := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa only [E, Metric.mem_closedBall, dist_zero_right] using hz
    simp only [D, Metric.mem_ball, dist_zero_right]
    change ‖(995 / 1000 : ℂ) * z‖ < 1
    rw [norm_mul]
    norm_num
    nlinarith only [hz1]
  have hi0 : Set.InjOn f0 E := (mul_right_injective₀ (by norm_num : (995 / 1000 : ℂ) ≠ 0)).injOn
  have h1 : Set.MapsTo f1 E D ∧ Set.InjOn f1 E := by
    simpa only [f1, contourRotation, mul_zero, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, one_mul] using hstep (91 / 100) 0 (by norm_num) (by norm_num) f0 hm0 hi0
  have h2 : Set.MapsTo f2 E D ∧ Set.InjOn f2 E :=
    hstep _ _ (by norm_num) (by norm_num) f1 h1.1 h1.2
  have h3 : Set.MapsTo f3 E D ∧ Set.InjOn f3 E :=
    hstep _ _ (by norm_num) (by norm_num) f2 h2.1 h2.2
  have h4 : Set.MapsTo f4 E D ∧ Set.InjOn f4 E :=
    hstep _ _ (by norm_num) (by norm_num) f3 h3.1 h3.2
  intro z hz w hw he
  have hL {u : ℂ} (hu : u ∈ E) : -contourRotation (-783 / 10000) * f4 u ∈ D := by
    simpa only [D, Metric.mem_ball, dist_zero_right, norm_mul, norm_neg,
      norm_contourRotation, one_mul] using h4.1 hu
  change -(77 / 100 : ℂ) * contourLuneMap (75 / 10)
      (-contourRotation (-783 / 10000) * f4 z) =
    -(77 / 100 : ℂ) * contourLuneMap (75 / 10)
      (-contourRotation (-783 / 10000) * f4 w) at he
  have hout := mul_left_cancel₀ (by norm_num : -(77 / 100 : ℂ) ≠ 0) he
  have hmid := injOn_contourLuneMap (by norm_num : (1 : ℝ) < 75 / 10) (hL hz) (hL hw) hout
  have hunit : -contourRotation (-783 / 10000) ≠ 0 := by
    apply neg_ne_zero.mpr
    apply norm_ne_zero_iff.mp
    rw [norm_contourRotation]
    norm_num
  exact h4.2 hz hw (mul_left_cancel₀ hunit hmid)

end DirichletL

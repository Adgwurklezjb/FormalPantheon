import Analysis.QProductAnalytic

/-!
CDT v2's level-two product, equation `defofh`, supplied TeX 6947-6948.
Meanings and the distinction from the level-six function precede these bodies in
-/

namespace DirichletL

/-- CDT's level-two product `-256*q*∏(1+q^n)^24`, with indices starting at one. -/
noncomputable def levelTwoHauptmodul (q : ℂ) : ℂ :=
  -256 * q * (∏' n : ℕ, (1 + q ^ (n + 1))) ^ 24

theorem levelTwoHauptmodul_zero : levelTwoHauptmodul 0 = 0 := by
  simp [levelTwoHauptmodul]

theorem analyticOnNhd_levelTwoHauptmodul :
    AnalyticOnNhd ℂ levelTwoHauptmodul (Metric.ball 0 1) := by
  have hp : AnalyticOnNhd ℂ (fun q : ℂ => ∏' n : ℕ, (1 + q ^ (n + 1)))
      (Metric.ball 0 1) := by
    have h := differentiableOn_tprod_one_add_mul_pow
      (s := (1 : ℂ)) (e := fun n => n + 1) (by simp) (fun _ => le_rfl)
    simpa only [one_mul] using h.analyticOnNhd Metric.isOpen_ball
  intro q hq
  exact (analyticAt_const.mul analyticAt_id).mul ((hp q hq).fun_pow 24)

theorem hasDerivAt_levelTwoHauptmodul_zero : HasDerivAt levelTwoHauptmodul (-256) 0 := by
  let T (q : ℂ) : ℂ := ∏' n : ℕ, (1 + q ^ (n + 1))
  have hT : DifferentiableAt ℂ T 0 := by
    have h := differentiableOn_tprod_one_add_mul_pow
      (s := (1 : ℂ)) (e := fun n => n + 1) (by simp) (fun _ => le_rfl)
    simpa only [one_mul, T] using h.differentiableAt (Metric.ball_mem_nhds 0 (by norm_num))
  have hT0 : T 0 = 1 := by simp [T]
  have hlinear : HasDerivAt (fun q : ℂ => -256 * q) (-256) 0 := by
    simpa only [mul_one] using (hasDerivAt_id (𝕜 := ℂ) 0).const_mul (-256)
  convert hlinear.mul (hT.hasDerivAt.pow 24) using 1
  simp [levelTwoHauptmodul, T, hT0]

theorem levelTwoHauptmodul_ne_zero_iff {q : ℂ} (hq : ‖q‖ < 1) :
    levelTwoHauptmodul q ≠ 0 ↔ q ≠ 0 := by
  have hT : (∏' n : ℕ, (1 + q ^ (n + 1))) ≠ 0 := by
    simpa only [one_mul] using tprod_one_add_mul_pow_ne_zero
      (s := (1 : ℂ)) (e := fun n => n + 1) (by simp) (fun _ => le_rfl) hq
  simp [levelTwoHauptmodul, hT]

end DirichletL

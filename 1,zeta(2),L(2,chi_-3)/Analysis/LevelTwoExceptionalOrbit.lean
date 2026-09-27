import Analysis.LevelTwoFiberBounds
import Analysis.LevelTwoFricke
import Analysis.LevelTwoCosets
import Analysis.LevelTwoLocalInjective

/-!
Completeness of the specific modular fiber used in CDT author Lemma A.4.4,
page 205. Meanings, action direction, and endpoint checks precede the bodies
-/

namespace DirichletL

open Complex Function.Periodic
open _root_.UpperHalfPlane hiding I
open scoped MatrixGroups

private theorem exists_T_zpow_smul_eq_of_qParam_eq (τ σ : ℍ)
    (h : Function.Periodic.qParam 1 τ = Function.Periodic.qParam 1 σ) :
    ∃ m : ℤ, (ModularGroup.T ^ m • τ : ℍ) = σ := by
  obtain ⟨m, hm⟩ := qParam_left_inv_mod_period (by norm_num : (1 : ℝ) ≠ 0) (τ : ℂ)
  obtain ⟨n, hn⟩ := qParam_left_inv_mod_period (by norm_num : (1 : ℝ) ≠ 0) (σ : ℂ)
  rw [← h] at hn
  simp only [Complex.ofReal_one, mul_one] at hm hn
  refine ⟨m - n, ?_⟩
  apply UpperHalfPlane.ext
  rw [ModularGroup.coe_T_zpow_smul_eq]
  push_cast
  linear_combination hn - hm

theorem levelTwoHauptmodul_S_ne_neg_one_div_seventyTwo {τ : ℍ}
    (hτ : 5 / 6 ≤ τ.im) :
    levelTwoHauptmodul
      (Function.Periodic.qParam 1 (ModularGroup.S • τ : ℍ)) ≠ -1 / 72 := by
  intro hvalue
  have hprod := levelTwoHauptmodul_S_mul_half τ
  rw [hvalue] at hprod
  have hhalf : levelTwoHauptmodul (qParam 1 ((τ : ℂ) / 2)) = -1152 := by
    linear_combination -72 * hprod
  have hbound := norm_levelTwoHauptmodul_le_sevenHundred
    (norm_qParam_one_half_le_of_im_ge hτ)
  rw [hhalf] at hbound
  norm_num at hbound

theorem levelTwoHauptmodul_exceptional_fiber_orbit {q0 : ℝ}
    (hq0 : q0 ∈ Set.Ioo 0 (1 / 10000))
    (hv0 : levelTwoHauptmodul (q0 : ℂ) = -1 / 72)
    (τ0 τ : ℍ) (hτ0 : Function.Periodic.qParam 1 τ0 = (q0 : ℂ))
    (hτ : levelTwoHauptmodul (Function.Periodic.qParam 1 τ) = -1 / 72) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 2 ∧ (γ • τ0 : ℍ) = τ := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  let σ : ℍ := g • τ
  have hheight : (5 / 6 : ℝ) ≤ σ.im := by
    have hsq : (3 : ℝ) ≤ 4 * σ.im ^ 2 :=
      ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg
    by_contra! hlt
    have hupper := pow_le_pow_left₀ σ.im_pos.le hlt.le 2
    norm_num at hupper
    nlinarith
  have hback : (g⁻¹ • σ : ℍ) = τ := by
    dsimp only [σ]
    exact inv_smul_smul g τ
  obtain ⟨δ, hδ, hcoset⟩ := exists_levelTwo_left_coset g⁻¹
  have hvalue (ρ : ℍ) (hρ : (δ • ρ : ℍ) = τ) :
      levelTwoHauptmodul (qParam 1 ρ) = -1 / 72 := by
    rw [← levelTwoHauptmodul_qParam_smul δ hδ ρ, hρ]
    exact hτ
  rcases hcoset with hc | hc | hc
  · have heq : (δ • σ : ℍ) = τ := by simpa only [hc] using hback
    have hσvalue := hvalue σ heq
    have hsmall : ‖qParam 1 σ‖ ≤ 1 / 1000 := by
      have hbound := mul_norm_le_norm_levelTwoHauptmodul
        (norm_qParam_one_le_of_im_ge hheight)
      rw [hσvalue] at hbound
      norm_num at hbound
      linarith
    have hq0norm : ‖(q0 : ℂ)‖ ≤ 1 / 1000 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0.1]
      exact hq0.2.le.trans (by norm_num)
    have hnome : qParam 1 σ = (q0 : ℂ) :=
      injOn_levelTwoHauptmodul_smallBall
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hsmall)
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hq0norm)
        (hσvalue.trans hv0.symm)
    obtain ⟨m, hm⟩ := exists_T_zpow_smul_eq_of_qParam_eq τ0 σ (hτ0.trans hnome.symm)
    have hT : ModularGroup.T ^ m ∈ CongruenceSubgroup.Gamma0 2 := by
      apply CongruenceSubgroup.Gamma0_mem.mpr
      have hrow : (ModularGroup.T ^ m) 1 0 = (0 : ℤ) := by
        change (ModularGroup.T ^ m).1 1 0 = 0
        rw [ModularGroup.coe_T_zpow]
        rfl
      rw [hrow]
      norm_num
    refine ⟨δ * ModularGroup.T ^ m, (CongruenceSubgroup.Gamma0 2).mul_mem hδ hT, ?_⟩
    rw [mul_smul, hm]
    exact heq
  · have heq : (δ • (ModularGroup.S • σ : ℍ) : ℍ) = τ := by
      simpa only [hc, mul_smul] using hback
    exact (levelTwoHauptmodul_S_ne_neg_one_div_seventyTwo hheight
      (hvalue (ModularGroup.S • σ : ℍ) heq)).elim
  · have heq : (δ • (ModularGroup.S • (ModularGroup.T • σ : ℍ) : ℍ) : ℍ) = τ := by
      simpa only [hc, mul_smul] using hback
    have hT : (5 / 6 : ℝ) ≤ (ModularGroup.T • σ : ℍ).im := by
      simpa only [ModularGroup.im_T_smul] using hheight
    exact (levelTwoHauptmodul_S_ne_neg_one_div_seventyTwo hT
      (hvalue (ModularGroup.S • (ModularGroup.T • σ : ℍ) : ℍ) heq)).elim

end DirichletL

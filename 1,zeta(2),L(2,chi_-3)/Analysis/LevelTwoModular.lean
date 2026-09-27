import Analysis.LevelTwoHauptmodul
import Analysis.DedekindEtaModular
import Analysis.DedekindEtaScaling

/-!
The level-two product and its invariance used in CDT author Lemma A.4.4,
pages 204-205. Meanings and normalization checks precede the bodies in
-/

namespace DirichletL

open Complex Function.Periodic
open _root_.UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm

theorem levelTwoHauptmodul_qParam_eq_eta (τ : ℍ) :
    levelTwoHauptmodul (Function.Periodic.qParam 1 τ) =
      -256 * dedekindEta (2 * (τ : ℂ)) ^ 24 / dedekindEta τ ^ 24 := by
  have hq : ‖qParam 1 τ‖ < 1 := by simpa using τ.norm_qParam_lt_one 1
  have hq0 : qParam 1 τ ≠ 0 := exp_ne_zero _
  have he0 : qEulerProduct (qParam 1 τ) ≠ 0 := qEulerProduct_ne_zero hq
  have hq2 : qParam 1 (2 * (τ : ℂ)) = qParam 1 τ ^ 2 := by
    simpa only [Nat.cast_ofNat] using qParam_one_nat_mul 2 τ
  have hprod : qEulerProduct (qParam 1 τ ^ 2) =
      qEulerProduct (qParam 1 τ) *
        (∏' n : ℕ, (1 + qParam 1 τ ^ (n + 1))) := by
    exact (tprod_one_sub_pow_mul_one_add_pow (e := fun n => n + 1)
      (fun _ => le_rfl) hq).symm
  rw [levelTwoHauptmodul]
  simp only [dedekindEta_pow_twenty_four_eq_qParam, hq2, hprod, mul_pow]
  field_simp [hq0, he0]

theorem levelTwoHauptmodul_qParam_smul (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 2) (τ : ℍ) :
    levelTwoHauptmodul (Function.Periodic.qParam 1 (γ • τ : ℍ)) =
      levelTwoHauptmodul (Function.Periodic.qParam 1 τ) := by
  have hc : (2 : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) 2).mp
      (CongruenceSubgroup.Gamma0_mem.mp hγ)
  obtain ⟨k, hk⟩ := hc
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  let A : SL(2, ℤ) := ⟨!![γ 0 0, 2 * γ 0 1; k, γ 1 1], by
    rw [Matrix.det_fin_two_of]
    rw [hk] at hdet
    nlinarith⟩
  have hkC : (k : ℂ) * 2 = (γ 1 0 : ℂ) := by
    exact_mod_cast (hk.trans (mul_comm (2 : ℤ) k)).symm
  have hσ : 0 < (2 * (τ : ℂ)).im := by
    simpa using mul_pos (by norm_num : (0 : ℝ) < 2) τ.im_pos
  let σ : ℍ := ⟨2 * (τ : ℂ), hσ⟩
  have hd : (A 1 0 : ℂ) * σ + (A 1 1 : ℂ) =
      (γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ) := by
    change (k : ℂ) * (2 * (τ : ℂ)) + (γ 1 1 : ℂ) = _
    rw [← mul_assoc, hkC]
  have hn : (A 0 0 : ℂ) * σ + (A 0 1 : ℂ) =
      2 * ((γ 0 0 : ℂ) * τ + (γ 0 1 : ℂ)) := by
    change (γ 0 0 : ℂ) * (2 * (τ : ℂ)) + ((2 * γ 0 1 : ℤ) : ℂ) = _
    push_cast
    ring
  have ha : ((A • σ : ℍ) : ℂ) = 2 * ((γ • τ : ℍ) : ℂ) := by
    simp only [coe_specialLinearGroup_apply, algebraMap_int_eq, Int.coe_castRingHom,
      Complex.ofReal_intCast]
    change ((A 0 0 : ℂ) * σ + (A 0 1 : ℂ)) /
      ((A 1 0 : ℂ) * σ + (A 1 1 : ℂ)) =
        2 * (((γ 0 0 : ℂ) * τ + (γ 0 1 : ℂ)) /
          ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)))
    rw [hd, hn, mul_div_assoc]
  have h1 : dedekindEta ((γ • τ : ℍ) : ℂ) ^ 24 =
      ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ 12 * dedekindEta τ ^ 24 := by
    simpa only [ModularGroup.denom_apply, dedekindEtaPowTwentyFourCuspForm_apply, zpow_ofNat] using
      SlashInvariantForm.slash_action_eqn_SL'' dedekindEtaPowTwentyFourCuspForm
        (CongruenceSubgroup.mem_Gamma_one γ) τ
  have h2 : dedekindEta (2 * ((γ • τ : ℍ) : ℂ)) ^ 24 =
      ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ 12 *
        dedekindEta (2 * (τ : ℂ)) ^ 24 := by
    have h := SlashInvariantForm.slash_action_eqn_SL'' dedekindEtaPowTwentyFourCuspForm
      (CongruenceSubgroup.mem_Gamma_one A) σ
    simp only [ModularGroup.denom_apply, dedekindEtaPowTwentyFourCuspForm_apply, zpow_ofNat] at h
    rw [ha, hd] at h
    exact h
  have hden : ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ≠ 0 := denom_ne_zero γ τ
  rw [levelTwoHauptmodul_qParam_eq_eta, levelTwoHauptmodul_qParam_eq_eta, h1, h2]
  rw [mul_left_comm (-256 : ℂ), mul_div_mul_left _ _ (pow_ne_zero 12 hden)]

end DirichletL

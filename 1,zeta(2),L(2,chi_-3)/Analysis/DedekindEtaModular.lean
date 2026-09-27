import Analysis.DedekindEtaTransformations
import Analysis.ModularSlash

/-!
The weight-12 cusp form eta^24, with the product normalization of DLMF
27.14.12-13. Its exact first-order behavior at infinity prepares the modular
vanishing argument for the level-six identities in CDT v2 Section 11.1.
-/

namespace DirichletL

open Complex Function.Periodic UpperHalfPlane
open scoped Real Topology Manifold MatrixGroups ModularForm CongruenceSubgroup

theorem dedekindEta_pow_twenty_four_eq_qParam (τ : ℂ) :
    dedekindEta τ ^ 24 = qParam 1 τ * qEulerProduct (qParam 1 τ) ^ 24 := by
  rw [dedekindEta, mul_pow, ← exp_nat_mul]
  congr 1
  simp only [qParam, ofReal_one, div_one]
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

private theorem tendsto_qParam_one_atImInfty :
    Filter.Tendsto (fun τ : ℍ => qParam 1 τ) atImInfty (𝓝 0) :=
  ((qParam_tendsto (h := 1) (by norm_num)).comp tendsto_coe_atImInfty).mono_right
    nhdsWithin_le_nhds

theorem tendsto_dedekindEta_pow_twenty_four_div_qParam :
    Filter.Tendsto (fun τ : ℍ => dedekindEta τ ^ 24 / qParam 1 τ)
      atImInfty (𝓝 1) := by
  have hc : ContinuousAt qEulerProduct 0 :=
    differentiableOn_qEulerProduct.continuousOn.continuousAt
      (Metric.isOpen_ball.mem_nhds (by simp))
  have ht := (hc.tendsto.comp tendsto_qParam_one_atImInfty).pow 24
  simp only [qEulerProduct_zero, one_pow] at ht
  convert ht using 1
  ext τ
  have hq : qParam 1 τ ≠ 0 := exp_ne_zero _
  simp only [Function.comp_apply, dedekindEta_pow_twenty_four_eq_qParam,
    mul_div_cancel_left₀ _ hq]

theorem isZeroAtImInfty_dedekindEta_pow_twenty_four :
    IsZeroAtImInfty (fun τ : ℍ => dedekindEta τ ^ 24) := by
  change Filter.Tendsto (fun τ : ℍ => dedekindEta τ ^ 24) atImInfty (𝓝 0)
  have ht := tendsto_dedekindEta_pow_twenty_four_div_qParam.mul
    tendsto_qParam_one_atImInfty
  simp only [mul_zero] at ht
  convert ht using 1
  ext τ
  have hq : qParam 1 τ ≠ 0 := exp_ne_zero _
  rw [div_mul_cancel₀ _ hq]

theorem dedekindEta_pow_twenty_four_slash (γ : SL(2, ℤ)) :
    (fun τ : ℍ => dedekindEta τ ^ 24) ∣[(12 : ℤ)] γ =
      (fun τ : ℍ => dedekindEta τ ^ 24) := by
  apply slashInvariant_of_S_of_T
  · ext τ
    apply (ModularForm.slash_action_eq'_iff _ _ _ _).mpr
    have h10 : ((ModularGroup.S 1 0 : ℤ) : ℂ) = 1 := by norm_num [ModularGroup.S]
    have h11 : ((ModularGroup.S 1 1 : ℤ) : ℂ) = 0 := by norm_num [ModularGroup.S]
    rw [modular_S_smul]
    simpa only [h10, h11, coe_mk, inv_neg, neg_div, one_div, one_mul, add_zero,
      zpow_ofNat] using
      dedekindEta_neg_inv_pow_twenty_four τ.im_pos
  · ext τ
    apply (ModularForm.slash_action_eq'_iff _ _ _ _).mpr
    have hT : ((ModularGroup.T • τ : ℍ) : ℂ) = τ + 1 := by
      simpa using ModularGroup.coe_T_zpow_smul_eq τ (n := 1)
    have h10 : ((ModularGroup.T 1 0 : ℤ) : ℂ) = 0 := by norm_num [ModularGroup.T]
    have h11 : ((ModularGroup.T 1 1 : ℤ) : ℂ) = 1 := by norm_num [ModularGroup.T]
    simpa only [hT, h10, h11, zero_mul, zero_add, one_zpow, one_mul] using
      dedekindEta_add_one_pow_twenty_four (τ : ℂ)

private theorem mdifferentiable_dedekindEta_pow_twenty_four :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => dedekindEta τ ^ 24) := by
  apply UpperHalfPlane.mdifferentiable_iff.mpr
  apply (differentiableOn_dedekindEta.pow 24).congr
  intro τ hτ
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hτ, coe_mk_subtype, Pi.pow_apply]

/-- Eta's 24th power as a level-one cusp form of weight 12. -/
noncomputable def dedekindEtaPowTwentyFourCuspForm : CuspForm Γ(1) 12 where
  toFun τ := dedekindEta τ ^ 24
  slash_action_eq' A hA := by
    obtain ⟨γ, _, rfl⟩ := hA
    change (fun τ : ℍ => dedekindEta τ ^ 24) ∣[(12 : ℤ)] γ = _
    exact dedekindEta_pow_twenty_four_slash γ
  holo' := mdifferentiable_dedekindEta_pow_twenty_four
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    apply (OnePoint.isZeroAt_iff_forall_SL2Z hc).mpr
    intro γ _
    simpa only [dedekindEta_pow_twenty_four_slash] using
      isZeroAtImInfty_dedekindEta_pow_twenty_four

@[simp] theorem dedekindEtaPowTwentyFourCuspForm_apply (τ : ℍ) :
    dedekindEtaPowTwentyFourCuspForm τ = dedekindEta τ ^ 24 := rfl

theorem dedekindEtaPowTwentyFourCuspForm_apply_ne_zero (τ : ℍ) :
    dedekindEtaPowTwentyFourCuspForm τ ≠ 0 :=
  pow_ne_zero _ (dedekindEta_ne_zero τ.im_pos)

end DirichletL

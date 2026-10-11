import Analysis.ThetaQuarticDifference
import Analysis.ModularVanishing

/-!
DLMF 20.7.5 for the existing normalized theta series, using the proved
weight-four vanishing criterion. This prepares the local square at the
CDT level-two quotient branch value 4. Meanings and coordinate checks
-/

namespace DirichletL

open Complex Function.Periodic UpperHalfPlane
open scoped Real Topology Manifold MatrixGroups ModularForm CongruenceSubgroup

private theorem qParam_two_eq_one_half (τ : ℂ) :
    Function.Periodic.qParam 2 τ = Function.Periodic.qParam 1 (τ / 2) := by
  simp only [qParam, ofReal_ofNat, ofReal_one, div_one]
  congr 1
  ring

private theorem qParam_two_sq (τ : ℂ) :
    Function.Periodic.qParam 2 τ ^ 2 = Function.Periodic.qParam 1 τ := by
  simp only [qParam, ofReal_ofNat, ofReal_one, div_one]
  rw [← exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  congr 1
  ring

private theorem thetaQuarticDifference_sq_slash (γ : SL(2, ℤ)) :
    (fun τ : ℍ => thetaQuarticDifference (Function.Periodic.qParam 2 τ) ^ 2)
        ∣[(4 : ℤ)] γ =
      (fun τ : ℍ => thetaQuarticDifference (Function.Periodic.qParam 2 τ) ^ 2) := by
  apply slashInvariant_of_S_of_T
  · ext τ
    apply (ModularForm.slash_action_eq'_iff _ _ _ _).mpr
    have h10 : ((ModularGroup.S 1 0 : ℤ) : ℂ) = 1 := by norm_num [ModularGroup.S]
    have h11 : ((ModularGroup.S 1 1 : ℤ) : ℂ) = 0 := by norm_num [ModularGroup.S]
    have hh : 0 < ((τ : ℂ) / 2).im := by simpa using half_pos τ.im_pos
    have hc : -1 / (4 * ((τ : ℂ) / 2)) = (-1 / (τ : ℂ)) / 2 := by
      field_simp
      ring
    have h := thetaQuarticDifference_inversion hh
    rw [hc] at h
    have hS : thetaQuarticDifference (qParam 2 (-1 / (τ : ℂ))) ^ 2 =
        (τ : ℂ) ^ 4 * thetaQuarticDifference (qParam 2 τ) ^ 2 := by
      rw [qParam_two_eq_one_half, qParam_two_eq_one_half, h]
      ring
    rw [modular_S_smul]
    simpa only [h10, h11, coe_mk, inv_neg, neg_div, one_div, one_mul, add_zero,
      zpow_ofNat] using hS
  · ext τ
    apply (ModularForm.slash_action_eq'_iff _ _ _ _).mpr
    have hT : ((ModularGroup.T • τ : ℍ) : ℂ) = τ + 1 := by
      simpa using ModularGroup.coe_T_zpow_smul_eq τ (n := 1)
    have h10 : ((ModularGroup.T 1 0 : ℤ) : ℂ) = 0 := by norm_num [ModularGroup.T]
    have h11 : ((ModularGroup.T 1 1 : ℤ) : ℂ) = 1 := by norm_num [ModularGroup.T]
    simp only [hT, h10, h11, zero_mul, zero_add, one_zpow, one_mul]
    rw [qParam_two_eq_one_half, qParam_two_eq_one_half,
      show ((τ : ℂ) + 1) / 2 = (τ : ℂ) / 2 + 1 / 2 by ring,
      thetaQuarticDifference_add_half (by simpa using half_pos τ.im_pos)]
    ring

private theorem mdifferentiable_thetaQuarticDifference_sq :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ => thetaQuarticDifference (Function.Periodic.qParam 2 τ) ^ 2) := by
  have hQ : Differentiable ℂ (qParam 2) := by
    change Differentiable ℂ (fun τ : ℂ => exp (2 * π * Complex.I * τ / 2))
    exact (((differentiable_const _).mul differentiable_id).div_const 2).cexp
  have hm : Set.MapsTo (qParam 2) {τ : ℂ | 0 < τ.im} (Metric.ball 0 1) := by
    intro τ hτ
    have h := (norm_qParam_lt_iff (h := 2) (by norm_num) 0 τ).mpr hτ
    simpa using h
  have hd := (analyticOnNhd_thetaQuarticDifference.differentiableOn.comp
    hQ.differentiableOn hm).fun_pow 2
  apply UpperHalfPlane.mdifferentiable_iff.mpr
  apply hd.congr
  intro τ hτ
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hτ, coe_mk_subtype]

private theorem isBoundedAtImInfty_thetaQuarticDifference_sq_div_qParam :
    IsBoundedAtImInfty (fun τ : ℍ =>
      thetaQuarticDifference (Function.Periodic.qParam 2 τ) ^ 2 /
        Function.Periodic.qParam 1 τ) := by
  have hd := (analyticOnNhd_thetaQuarticDifference 0 (by simp)).differentiableAt.hasDerivAt
  have ht : Filter.Tendsto (fun q : ℂ => thetaQuarticDifference q / q)
      (𝓝[≠] 0) (𝓝 (deriv thetaQuarticDifference 0)) := by
    simpa only [zero_add, thetaQuarticDifference_zero, sub_zero, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero
  have hq := (qParam_tendsto (h := 2) (by norm_num)).comp tendsto_coe_atImInfty
  have hb := ((ht.comp hq).pow 2).isBigO_one ℝ
  change Asymptotics.IsBigO atImInfty _ (fun _ => (1 : ℝ))
  convert hb using 1
  ext τ
  simp only [Function.comp_apply, div_pow, qParam_two_sq]

theorem thetaQuarticDifference_eq_zero {q : ℂ} (hq : ‖q‖ < 1) :
    thetaQuarticDifference q = 0 := by
  have hb : IsBoundedAtImInfty
      (fun τ : ℍ => thetaQuarticDifference (qParam 2 τ) ^ 2) := by
    have hqzero := ((qParam_tendsto (h := 1) (by norm_num)).comp
      tendsto_coe_atImInfty).mono_right nhdsWithin_le_nhds
    have h := Filter.BoundedAtFilter.mul
      isBoundedAtImInfty_thetaQuarticDifference_sq_div_qParam (hqzero.isBigO_one ℝ)
    convert h using 1
    ext τ
    simp only [Pi.mul_apply, Function.comp_apply]
    exact (div_mul_cancel₀ _ (exp_ne_zero _ : qParam 1 τ ≠ 0)).symm
  let f : ModularForm Γ(1) 4 :=
    { toFun := fun τ => thetaQuarticDifference (qParam 2 τ) ^ 2
      slash_action_eq' := fun γ hγ => by
        obtain ⟨γ, _, rfl⟩ := hγ
        exact thetaQuarticDifference_sq_slash γ
      holo' := mdifferentiable_thetaQuarticDifference_sq
      bdd_at_cusps' := isBoundedAt_cusp_of_slash_SL2 (fun γ => by
        simpa only [SlashInvariantForm.coe_mk, thetaQuarticDifference_sq_slash] using hb) }
  have hf : f = 0 := levelOne_eq_zero_of_bounded_div_qParam_pow (n := 1)
    (by norm_num) f (by
      simpa only [pow_one] using isBoundedAtImInfty_thetaQuarticDifference_sq_div_qParam)
  have hzero (τ : ℍ) : thetaQuarticDifference (qParam 2 τ) = 0 := by
    have h : thetaQuarticDifference (qParam 2 τ) ^ 2 = 0 :=
      congrArg (fun F : ModularForm Γ(1) 4 => F τ) hf
    exact sq_eq_zero_iff.mp h
  by_cases hq0 : q = 0
  · simpa only [hq0] using thetaQuarticDifference_zero
  · let τ : ℍ := ⟨invQParam 2 q,
      im_invQParam_pos_of_norm_lt_one (by norm_num : (0 : ℝ) < 2) hq hq0⟩
    have hroot := hzero τ
    change thetaQuarticDifference (qParam 2 (invQParam 2 q)) = 0 at hroot
    rwa [qParam_right_inv (by norm_num : (2 : ℝ) ≠ 0) hq0] at hroot

theorem sum_complexSeries_theta_quartic {q : ℂ} (hq : ‖q‖ < 1) :
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum q ^ 4 -
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum q ^ 4 =
      q * (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)).sum q ^ 4 := by
  exact sub_eq_zero.mp (thetaQuarticDifference_eq_zero hq)

end DirichletL

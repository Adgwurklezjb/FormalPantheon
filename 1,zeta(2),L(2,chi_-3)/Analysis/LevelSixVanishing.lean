import Analysis.LevelSixNorm
import Analysis.LevelSixModularForms
import Analysis.ModularVanishing

/-!
The level-six order-of-vanishing criterion for the modular identities in
CDT v2 Section 11.1. A form of weight k is zero when it vanishes to order
n > k at infinity, by the twelve-factor level-one norm.
-/

namespace DirichletL

open Complex Function.Periodic UpperHalfPlane
open scoped Topology Manifold MatrixGroups ModularForm

theorem isBoundedAtImInfty_levelSixNorm_div_qParam_pow {k : ℤ} {n : ℕ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 6) k)
    (hf : IsBoundedAtImInfty (fun τ : ℍ => f τ / qParam 1 τ ^ n)) :
    IsBoundedAtImInfty (fun τ : ℍ => levelSixNorm f τ / qParam 1 τ ^ n) := by
  have hb := isBoundedAtImInfty_finset_prod (Finset.univ.erase (0 : Fin 12))
    (fun i => ⇑f ∣[k] levelSixRep i)
    (fun i _ => ModularFormClass.bdd_at_infty_slash f (levelSixRep i))
  convert Filter.BoundedAtFilter.mul hf hb using 1
  ext τ
  rw [levelSixNorm_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : Fin 12))]
  simp only [levelSixRep_zero, SlashAction.slash_one, Pi.mul_apply]
  ring

theorem levelSix_eq_zero_of_bounded_div_qParam_pow {k : ℤ} {n : ℕ}
    (hk : k < (n : ℤ)) (f : ModularForm (CongruenceSubgroup.Gamma0 6) k)
    (hf : IsBoundedAtImInfty (fun τ : ℍ => f τ / qParam 1 τ ^ n)) : f = 0 := by
  apply (levelSixNorm_eq_zero_iff f).mp
  exact levelOne_eq_zero_of_bounded_div_qParam_pow (by omega) (levelSixNorm f)
    (isBoundedAtImInfty_levelSixNorm_div_qParam_pow f hf)

theorem levelSix_eq_zero_of_finite_checks {k : ℤ} {n : ℕ}
    (hk : k < (n : ℤ)) (f : ℍ → ℂ)
    (hS : ∀ i, f ∣[k] (levelSixRep i * ModularGroup.S *
      (levelSixRep (levelSixPermS i))⁻¹) = f)
    (hT : ∀ i, f ∣[k] (levelSixRep i * ModularGroup.T *
      (levelSixRep (levelSixPermT i))⁻¹) = f)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbdd : ∀ i : Fin 12, IsBoundedAtImInfty (f ∣[k] levelSixRep i))
    (horder : IsBoundedAtImInfty (fun τ : ℍ => f τ / qParam 1 τ ^ n)) : f = 0 := by
  have hz := levelSix_eq_zero_of_bounded_div_qParam_pow hk
    (levelSixModularForm k f hS hT hhol hbdd) horder
  exact congrArg (fun F : ModularForm (CongruenceSubgroup.Gamma0 6) k => (F : ℍ → ℂ)) hz

theorem levelSix_periodic_comp_ofComplex {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 6) k) :
    Function.Periodic (f ∘ ofComplex) 1 := by
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 6 := by
    rw [CongruenceSubgroup.Gamma0_mem]
    decide
  have he (τ : ℍ) : f (ModularGroup.T • τ) = f τ := by
    have h10 : ((ModularGroup.T 1 0 : ℤ) : ℂ) = 0 := by norm_num [ModularGroup.T]
    have h11 : ((ModularGroup.T 1 1 : ℤ) : ℂ) = 1 := by norm_num [ModularGroup.T]
    simpa only [ModularGroup.denom_apply, h10, h11, zero_mul, zero_add, one_zpow, one_mul] using
      SlashInvariantForm.slash_action_eqn_SL'' f hT τ
  intro z
  by_cases hz : 0 < z.im
  · have hz1 : 0 < (z + 1).im := by simpa only [add_im, one_im, add_zero] using hz
    have hτ : ofComplex (z + 1) = ModularGroup.T • ofComplex z := by
      apply UpperHalfPlane.ext
      have h := ModularGroup.coe_T_zpow_smul_eq (ofComplex z) (n := 1)
      simpa only [zpow_one, Int.cast_one, ofComplex_apply_of_im_pos hz,
        ofComplex_apply_of_im_pos hz1, coe_mk_subtype] using h.symm
    simpa only [Function.comp_apply, hτ] using he (ofComplex z)
  · have hz1 : (z + 1).im ≤ 0 := by
      simpa only [add_im, one_im, add_zero] using (not_lt.mp hz)
    simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos hz1,
      ofComplex_apply_of_im_nonpos (not_lt.mp hz)]

theorem levelSix_eq_cuspFunction {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 6) k) (τ : ℍ) :
    SlashInvariantFormClass.cuspFunction 1 f (qParam 1 τ) = f τ := by
  simpa only [SlashInvariantFormClass.cuspFunction, Nat.cast_one, Function.comp_apply,
    ofComplex_apply] using
    (levelSix_periodic_comp_ofComplex f).eq_cuspFunction (by norm_num : (1 : ℝ) ≠ 0) τ

theorem levelSix_differentiableAt_cuspFunction {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 6) k) {q : ℂ} (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ (SlashInvariantFormClass.cuspFunction 1 f) q := by
  simp only [SlashInvariantFormClass.cuspFunction, Nat.cast_one]
  rcases eq_or_ne q 0 with rfl | hq0
  · exact (levelSix_periodic_comp_ofComplex f).differentiableAt_cuspFunction_zero
      (by norm_num : (0 : ℝ) < 1)
      (Filter.eventually_of_mem (Filter.preimage_mem_comap (Filter.Ioi_mem_atTop 0))
        (fun _ => ModularFormClass.differentiableAt_comp_ofComplex f))
      (ModularFormClass.bounded_at_infty_comp_ofComplex f)
  · exact qParam_right_inv (by norm_num : (1 : ℝ) ≠ 0) hq0 ▸
      (levelSix_periodic_comp_ofComplex f).differentiableAt_cuspFunction
        (by norm_num : (1 : ℝ) ≠ 0)
        (ModularFormClass.differentiableAt_comp_ofComplex f
          (im_invQParam_pos_of_norm_lt_one (by norm_num : (0 : ℝ) < 1) hq hq0))

theorem levelSix_analyticAt_cuspFunction_zero {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 6) k) :
    AnalyticAt ℂ (SlashInvariantFormClass.cuspFunction 1 f) 0 :=
  DifferentiableOn.analyticAt
    (fun q hq => (levelSix_differentiableAt_cuspFunction f hq).differentiableWithinAt)
    (by simpa only [ball_zero_eq] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

theorem levelSix_eq_zero_of_qExpansion_coeff_eq_zero {k : ℤ} {n : ℕ}
    (hk : k < (n : ℤ)) (f : ModularForm (CongruenceSubgroup.Gamma0 6) k)
    (hf : ∀ m < n, (ModularFormClass.qExpansion 1 f).coeff m = 0) : f = 0 := by
  apply levelSix_eq_zero_of_bounded_div_qParam_pow hk f
  have hc : ∀ m < n,
      (FormalMultilinearSeries.ofScalars ℂ (fun j =>
        iteratedDeriv j (SlashInvariantFormClass.cuspFunction 1 f) 0 / j.factorial)).coeff m =
      0 := by
    intro m hm
    simpa only [FormalMultilinearSeries.coeff_ofScalars, ModularFormClass.qExpansion_coeff,
      div_eq_mul_inv, mul_comm] using hf m hm
  have ht := tendsto_div_pow_of_hasFPowerSeriesAt
    (levelSix_analyticAt_cuspFunction_zero f).hasFPowerSeriesAt hc
  have hq := (qParam_tendsto (h := 1) (by norm_num)).comp tendsto_coe_atImInfty
  change Asymptotics.IsBigO atImInfty _ (fun _ => (1 : ℝ))
  simpa only [Function.comp_def, levelSix_eq_cuspFunction] using (ht.comp hq).isBigO_one ℝ

end DirichletL

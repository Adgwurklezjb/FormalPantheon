import Analysis.DedekindEtaModular

/-!
A level-one modular form of weight k vanishes if its first n Fourier
coefficients vanish and k < 12*n. Division by the normalized eta cusp form
reduces this to Mathlib's negative-weight theorem. This prepares the finite
index argument for the modular identities in CDT v2 Section 11.1.
-/

namespace DirichletL

open Complex Function.Periodic UpperHalfPlane
open scoped Topology Manifold MatrixGroups ModularForm CongruenceSubgroup

private theorem modularForm_div_eta_pow_slash {k : ℤ} (f : ModularForm Γ(1) k)
    (n : ℕ) (γ : SL(2, ℤ)) :
    (fun τ : ℍ => f τ / dedekindEtaPowTwentyFourCuspForm τ ^ n) ∣[k - 12 * (n : ℤ)] γ =
      (fun τ : ℍ => f τ / dedekindEtaPowTwentyFourCuspForm τ ^ n) := by
  ext τ
  apply (ModularForm.slash_action_eq'_iff _ _ _ _).mpr
  have hγ := CongruenceSubgroup.mem_Gamma_one γ
  have hJ : ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ≠ 0 := by
    simpa only [ModularGroup.denom_apply] using denom_ne_zero γ τ
  rw [SlashInvariantForm.slash_action_eqn_SL'' f hγ τ,
    SlashInvariantForm.slash_action_eqn_SL'' dedekindEtaPowTwentyFourCuspForm hγ τ,
    ModularGroup.denom_apply,
    mul_pow, zpow_sub₀ hJ]
  have hp : (((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ (12 : ℤ)) ^ n =
      ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ (12 * (n : ℤ)) := by
    simpa only [zpow_natCast] using
      (zpow_mul ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) (12 : ℤ) (n : ℤ)).symm
  rw [hp]
  ring

private theorem mdifferentiable_modularForm_div_eta_pow {k : ℤ}
    (f : ModularForm Γ(1) k) (n : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ => f τ / dedekindEtaPowTwentyFourCuspForm τ ^ n) := by
  apply UpperHalfPlane.mdifferentiable_iff.mpr
  exact (UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)).div
    ((UpperHalfPlane.mdifferentiable_iff.mp
      (CuspFormClass.holo dedekindEtaPowTwentyFourCuspForm)).pow n)
    (fun τ _ => pow_ne_zero n (dedekindEtaPowTwentyFourCuspForm_apply_ne_zero
      (ofComplex τ)))

private theorem isBoundedAtImInfty_modularForm_div_eta_pow {k : ℤ}
    (f : ModularForm Γ(1) k) (n : ℕ)
    (hf : IsBoundedAtImInfty (fun τ : ℍ => f τ / qParam 1 τ ^ n)) :
    IsBoundedAtImInfty (fun τ : ℍ => f τ / dedekindEtaPowTwentyFourCuspForm τ ^ n) := by
  have ht := (tendsto_dedekindEta_pow_twenty_four_div_qParam.pow n).inv₀ (by simp)
  have hb := Filter.BoundedAtFilter.mul hf (ht.isBigO_one ℝ)
  change Filter.BoundedAtFilter atImInfty _
  convert hb using 1
  ext τ
  have hq : qParam 1 τ ≠ 0 := exp_ne_zero _
  have he : dedekindEta τ ≠ 0 := dedekindEta_ne_zero τ.im_pos
  simp only [Pi.mul_apply, dedekindEtaPowTwentyFourCuspForm_apply, div_pow]
  field_simp [hq, he]

theorem levelOne_eq_zero_of_bounded_div_qParam_pow {k : ℤ} {n : ℕ}
    (hk : k < 12 * (n : ℤ)) (f : ModularForm Γ(1) k)
    (hf : IsBoundedAtImInfty (fun τ : ℍ => f τ / qParam 1 τ ^ n)) : f = 0 := by
  let g : ModularForm Γ(1) (k - 12 * (n : ℤ)) :=
    { toFun := fun τ => f τ / dedekindEtaPowTwentyFourCuspForm τ ^ n
      slash_action_eq' := fun γ hγ => by
        obtain ⟨γ, _, rfl⟩ := hγ
        exact modularForm_div_eta_pow_slash f n γ
      holo' := mdifferentiable_modularForm_div_eta_pow f n
      bdd_at_cusps' := isBoundedAt_cusp_of_slash_SL2 (fun γ => by
        simpa only [SlashInvariantForm.coe_mk, modularForm_div_eta_pow_slash] using
          isBoundedAtImInfty_modularForm_div_eta_pow f n hf) }
  have hg : (g : ℍ → ℂ) = 0 :=
    ModularFormClass.levelOne_neg_weight_eq_zero (sub_neg.mpr hk) g
  apply ModularForm.ext
  intro τ
  have hz : f τ / dedekindEtaPowTwentyFourCuspForm τ ^ n = 0 := congrFun hg τ
  exact (div_eq_zero_iff.mp hz).resolve_right (pow_ne_zero n
    (dedekindEtaPowTwentyFourCuspForm_apply_ne_zero τ))

theorem tendsto_div_pow_of_hasFPowerSeriesAt {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {n : ℕ} (hf : HasFPowerSeriesAt f p 0)
    (hp : ∀ m < n, p.coeff m = 0) :
    Filter.Tendsto (fun z => f z / z ^ n) (𝓝[≠] 0) (𝓝 (p.coeff n)) := by
  let g := (Function.swap dslope 0)^[n] f
  have hg := hf.has_fpower_series_iterate_dslope_fslope n
  have hg0 : g 0 = p.coeff n := by
    have h := hg.coeff_zero 1
    change (FormalMultilinearSeries.fslope^[n] p).coeff 0 = g 0 at h
    simpa only [FormalMultilinearSeries.coeff_iterate_fslope, zero_add] using h.symm
  have he : ∀ᶠ z in 𝓝 (0 : ℂ), f z = z ^ n * g z := by
    filter_upwards [hasFPowerSeriesAt_iff'.mp hf, hasFPowerSeriesAt_iff'.mp hg]
      with z hz hzg
    simp only [sub_zero, FormalMultilinearSeries.coeff_iterate_fslope] at hz hzg
    obtain ⟨s, hs, hsum⟩ := hz.exists_hasSum_smul_of_apply_eq_zero hp
    have hgs : g z = s := hzg.unique hsum
    simpa only [smul_eq_mul, hgs] using hs.symm
  have ht : Filter.Tendsto g (𝓝[≠] 0) (𝓝 (p.coeff n)) := by
    rw [← hg0]
    exact hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hz0
  have h0 : z ≠ 0 := hz0
  rw [hz, mul_div_cancel_left₀ _ (pow_ne_zero n h0)]

theorem levelOne_eq_zero_of_qExpansion_coeff_eq_zero {k : ℤ} {n : ℕ}
    (hk : k < 12 * (n : ℤ)) (f : ModularForm Γ(1) k)
    (hf : ∀ m < n, (ModularFormClass.qExpansion 1 f).coeff m = 0) : f = 0 := by
  apply levelOne_eq_zero_of_bounded_div_qParam_pow hk f
  have hc : ∀ m < n, (ModularFormClass.qExpansionFormalMultilinearSeries 1 f).coeff m = 0 := by
    intro m hm
    simp [FormalMultilinearSeries.coeff, ModularFormClass.qExpansionFormalMultilinearSeries,
      hf m hm]
  have ht := tendsto_div_pow_of_hasFPowerSeriesAt
    (ModularFormClass.hasFPowerSeries_cuspFunction 1 f).hasFPowerSeriesAt hc
  have hq := (qParam_tendsto (h := 1) (by norm_num)).comp tendsto_coe_atImInfty
  have hb := (ht.comp hq).isBigO_one ℝ
  have he (τ : ℍ) : SlashInvariantFormClass.cuspFunction 1 f (qParam 1 τ) = f τ := by
    simpa only [Nat.cast_one] using SlashInvariantFormClass.eq_cuspFunction 1 f τ
  change Asymptotics.IsBigO atImInfty _ (fun _ => (1 : ℝ))
  simpa only [Function.comp_def, he] using hb

end DirichletL

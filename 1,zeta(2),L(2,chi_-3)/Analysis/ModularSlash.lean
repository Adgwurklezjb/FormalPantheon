import Mathlib

/-!
Slash-action and finite-product infrastructure for the modular identities
in CDT v2 Section 11.1. The group law is a right action; finite products
add their integer weights, including the weight-zero empty product.
-/

namespace DirichletL

open Complex UpperHalfPlane
open scoped Topology Manifold MatrixGroups ModularForm

/-- Bounds for all integral slash translates give boundedness at every arithmetic cusp. -/
theorem isBoundedAt_cusp_of_slash_SL2 {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {k : ℤ} {f : ℍ → ℂ} (hf : ∀ A : SL(2, ℤ), IsBoundedAtImInfty (f ∣[k] A))
    {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsBoundedAt f k := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  exact (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr (fun A _ => hf A)

theorem slash_eq_smul_iff (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (c : ℂ) :
    f ∣[k] γ = c • f ↔ ∀ τ : ℍ,
      f (γ • τ) = c * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ k * f τ := by
  rw [funext_iff]
  apply forall_congr'
  intro τ
  have hd : ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ≠ 0 :=
    denom_ne_zero γ τ
  simp only [ModularForm.SL_slash_def, Pi.smul_apply,
    smul_eq_mul, UpperHalfPlane.denom, zpow_neg]
  change f (γ • τ) * (((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ k)⁻¹ = c * f τ ↔ _
  rw [mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero k hd)]
  rw [mul_right_comm c (f τ)]

theorem slash_zpow_of_eq_smul (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) {c : ℂ}
    (hc : c ≠ 0) (h : f ∣[k] γ = c • f) (n : ℤ) : f ∣[k] (γ ^ n) = c ^ n • f := by
  have hnat (m : ℕ) : f ∣[k] (γ ^ m) = c ^ m • f := by
    induction m with
    | zero => simp
    | succ m hm =>
      simp only [pow_succ, SlashAction.slash_mul, hm, ModularForm.SL_smul_slash, h, smul_smul]
  cases n with
  | ofNat m => simpa only [Int.ofNat_eq_coe, zpow_natCast] using hnat m
  | negSucc m =>
    have he := congrArg (fun F : ℍ → ℂ =>
      (c ^ (m + 1))⁻¹ • (F ∣[k] ((γ ^ (m + 1))⁻¹))) (hnat (m + 1))
    simpa only [zpow_negSucc, ModularForm.SL_smul_slash, ← SlashAction.slash_mul,
      mul_inv_cancel, SlashAction.slash_one, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero _ hc), one_smul] using he.symm

theorem slashInvariant_of_S_of_T (k : ℤ) (f : ℍ → ℂ)
    (hS : f ∣[k] ModularGroup.S = f) (hT : f ∣[k] ModularGroup.T = f)
    (γ : SL(2, ℤ)) : f ∣[k] γ = f := by
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]
    trivial
  induction hγ using Subgroup.closure_induction with
  | mem γ hγ =>
    rcases Set.mem_insert_iff.mp hγ with rfl | hγ
    · exact hS
    · obtain rfl := Set.mem_singleton_iff.mp hγ
      exact hT
  | one => simp
  | mul γ δ _ _ hγ hδ => rw [SlashAction.slash_mul, hγ, hδ]
  | inv γ _ hγ =>
    have h := SlashAction.slash_mul k γ γ⁻¹ f
    simpa only [mul_inv_cancel, SlashAction.slash_one, hγ] using h.symm

theorem mdifferentiable_slash_SL2 {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (k : ℤ) (γ : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ∣[k] γ) := by
  let A : GL(2, ℝ)⁺ := γ
  let N : ℂ → ℂ := fun z => (A 0 0 : ℂ) * z + (A 0 1 : ℂ)
  let D : ℂ → ℂ := fun z => (A 1 0 : ℂ) * z + (A 1 1 : ℂ)
  let M : ℂ → ℂ := fun z => N z / D z
  have hN : Differentiable ℂ N :=
    ((differentiable_const _).mul differentiable_id).add (differentiable_const _)
  have hD : Differentiable ℂ D :=
    ((differentiable_const _).mul differentiable_id).add (differentiable_const _)
  have hD0 : ∀ z : ℂ, 0 < z.im → D z ≠ 0 := fun z hz =>
    denom_ne_zero A ⟨z, hz⟩
  have hM (τ : ℍ) : M τ = ((A • τ : ℍ) : ℂ) := by
    simpa [M, N, D] using (coe_smul_of_det_pos A.property τ).symm
  have hdiffM : DifferentiableOn ℂ M {z : ℂ | 0 < z.im} :=
    hN.differentiableOn.div hD.differentiableOn hD0
  have hmaps : Set.MapsTo M {z : ℂ | 0 < z.im} {z : ℂ | 0 < z.im} := by
    intro z hz
    let τ : ℍ := ⟨z, hz⟩
    change 0 < (M τ).im
    rw [hM]
    exact (A • τ : ℍ).im_pos
  have hF := UpperHalfPlane.mdifferentiable_iff.mp hf
  have hdiff : DifferentiableOn ℂ
      (fun z => f (ofComplex (M z)) * D z ^ (-k)) {z : ℂ | 0 < z.im} :=
    (hF.comp hdiffM hmaps).mul (hD.differentiableOn.zpow (Or.inl hD0))
  apply UpperHalfPlane.mdifferentiable_iff.mpr
  apply hdiff.congr
  intro z hz
  let τ : ℍ := ⟨z, hz⟩
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz,
    ModularForm.SL_slash_def]
  change f (A • τ) * D τ ^ (-k) = f (ofComplex (M τ)) * D τ ^ (-k)
  rw [hM, ofComplex_apply]

theorem slash_SL2_eq_zero_iff (k : ℤ) (γ : SL(2, ℤ)) (f : ℍ → ℂ) :
    f ∣[k] γ = 0 ↔ f = 0 := by
  constructor
  · intro h
    have he := congrArg (fun F : ℍ → ℂ => F ∣[k] γ⁻¹) h
    simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one,
      SlashAction.zero_slash] using he
  · rintro rfl
    simp

theorem finset_prod_slash_SL2 {ι : Type*} (s : Finset ι) (k : ι → ℤ)
    (f : ι → ℍ → ℂ) (γ : SL(2, ℤ)) :
    (fun τ => ∏ i ∈ s, f i τ) ∣[∑ i ∈ s, k i] γ =
      (fun τ => ∏ i ∈ s, (f i ∣[k i] γ) τ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty, Finset.sum_empty] using ModularForm.is_invariant_one γ
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    change (f i * (fun τ => ∏ j ∈ s, f j τ)) ∣[k i + ∑ j ∈ s, k j] γ = _
    rw [ModularForm.mul_slash_SL2, ih]
    rfl

theorem mdifferentiable_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ)
    (hf : ∀ i ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => ∏ i ∈ s, f i τ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (mdifferentiable_const (c := (1 : ℂ)))
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).mul
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem isBoundedAtImInfty_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ)
    (hf : ∀ i ∈ s, IsBoundedAtImInfty (f i)) :
    IsBoundedAtImInfty (fun τ => ∏ i ∈ s, f i τ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Filter.const_boundedAtFilter atImInfty (1 : ℂ)
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi, Pi.mul_apply] using
      Filter.BoundedAtFilter.mul (hf i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end DirichletL

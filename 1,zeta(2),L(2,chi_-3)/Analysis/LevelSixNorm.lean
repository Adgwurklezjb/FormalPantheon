import Arithmetic.LevelSixMatrices
import Analysis.ModularSlash

/-!
A twelve-factor norm from Gamma0(6) to the full modular group, preparing
the finite coefficient checks for CDT v2 Section 11.1. The explicit S/T
certificates control the right slash action and the resulting weight.
-/

namespace DirichletL

open Complex UpperHalfPlane
open scoped Topology Manifold MatrixGroups ModularForm CongruenceSubgroup

private theorem levelSix_product_slash_generator {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 6) k) (A : SL(2, ℤ))
    (p : Equiv.Perm (Fin 12))
    (hp : ∀ i, levelSixRep i * A * (levelSixRep (p i))⁻¹ ∈
      CongruenceSubgroup.Gamma0 6) :
    (fun τ => ∏ i : Fin 12, (⇑f ∣[k] levelSixRep i) τ) ∣[12 * k] A =
      (fun τ => ∏ i : Fin 12, (⇑f ∣[k] levelSixRep i) τ) := by
  have he (i : Fin 12) :
      (⇑f ∣[k] levelSixRep i) ∣[k] A = ⇑f ∣[k] levelSixRep (p i) := by
    rw [← SlashAction.slash_mul]
    rw [show levelSixRep i * A =
      (levelSixRep i * A * (levelSixRep (p i))⁻¹) * levelSixRep (p i) by simp]
    have hinv := SlashInvariantForm.slash_action_eqn f
      ((levelSixRep i * A * (levelSixRep (p i))⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)
      ⟨levelSixRep i * A * (levelSixRep (p i))⁻¹, hp i, rfl⟩
    change ⇑f ∣[k] (levelSixRep i * A * (levelSixRep (p i))⁻¹) = ⇑f at hinv
    rw [SlashAction.slash_mul, hinv]
  have hw : (∑ _i : Fin 12, k) = 12 * k := by simp
  rw [← hw, finset_prod_slash_SL2]
  simp_rw [he]
  ext τ
  exact Equiv.prod_comp p (fun i => (⇑f ∣[k] levelSixRep i) τ)

private theorem levelSix_product_slash {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 6) k) (A : SL(2, ℤ)) :
    (fun τ => ∏ i : Fin 12, (⇑f ∣[k] levelSixRep i) τ) ∣[12 * k] A =
      (fun τ => ∏ i : Fin 12, (⇑f ∣[k] levelSixRep i) τ) := by
  apply slashInvariant_of_S_of_T
  · exact levelSix_product_slash_generator f ModularGroup.S levelSixPermS
      levelSixRep_mul_S_mem
  · exact levelSix_product_slash_generator f ModularGroup.T levelSixPermT
      levelSixRep_mul_T_mem

/-- The product of twelve fixed slash translates, as a level-one modular form. -/
noncomputable def levelSixNorm {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 6) k) : ModularForm Γ(1) (12 * k) where
  toFun τ := ∏ i : Fin 12, (⇑f ∣[k] levelSixRep i) τ
  slash_action_eq' A hA := by
    obtain ⟨A, _, rfl⟩ := hA
    exact levelSix_product_slash f A
  holo' := mdifferentiable_finset_prod Finset.univ _
    (fun i _ => mdifferentiable_slash_SL2 (ModularFormClass.holo f) k (levelSixRep i))
  bdd_at_cusps' := isBoundedAt_cusp_of_slash_SL2 (fun A => by
    simpa only [SlashInvariantForm.coe_mk, levelSix_product_slash] using
      isBoundedAtImInfty_finset_prod Finset.univ _
        (fun i _ => ModularFormClass.bdd_at_infty_slash f (levelSixRep i)))

@[simp] theorem levelSixNorm_apply {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 6) k) (τ : ℍ) :
    levelSixNorm f τ = ∏ i : Fin 12, (⇑f ∣[k] levelSixRep i) τ := rfl

private theorem exists_eq_zero_of_analytic_finset_prod_eq_zero {ι : Type*}
    (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, AnalyticOnNhd ℂ (f i) {z : ℂ | 0 < z.im})
    (hp : ∀ z : ℂ, 0 < z.im → ∏ i ∈ s, f i z = 0) :
    ∃ i ∈ s, ∀ z : ℂ, 0 < z.im → f i z = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hp Complex.I (by simp)
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, AnalyticOnNhd ℂ (f j) {z : ℂ | 0 < z.im} :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hmul : ∀ z : ℂ, 0 < z.im → f i z * ∏ j ∈ s, f j z = 0 := by
      simpa only [Finset.prod_insert hi] using hp
    have hprod : AnalyticOnNhd ℂ (fun z => ∏ j ∈ s, f j z) {z : ℂ | 0 < z.im} :=
      s.analyticOnNhd_fun_prod hs
    rcases (hf i (Finset.mem_insert_self _ _)).eq_zero_or_eq_zero_of_mul_eq_zero
      hprod hmul (convex_halfSpace_im_gt 0).isPreconnected with h | h
    · exact ⟨i, Finset.mem_insert_self _ _, h⟩
    · obtain ⟨j, hj, hz⟩ := ih hs h
      exact ⟨j, Finset.mem_insert_of_mem hj, hz⟩

theorem levelSixNorm_eq_zero_iff {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 6) k) : levelSixNorm f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have ha (i : Fin 12) : AnalyticOnNhd ℂ
        ((⇑f ∣[k] levelSixRep i) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
      (UpperHalfPlane.mdifferentiable_iff.mp
        (mdifferentiable_slash_SL2 (ModularFormClass.holo f) k (levelSixRep i))).analyticOnNhd
        (continuous_im.isOpen_preimage _ isOpen_Ioi)
    have hp : ∀ z : ℂ, 0 < z.im →
        ∏ i : Fin 12, ((⇑f ∣[k] levelSixRep i) ∘ ofComplex) z = 0 := by
      intro z _
      have hz := congrArg (fun F : ModularForm Γ(1) (12 * k) => F (ofComplex z)) h
      simpa only [levelSixNorm_apply, ModularForm.zero_apply, Function.comp_apply] using hz
    obtain ⟨i, _, hi⟩ := exists_eq_zero_of_analytic_finset_prod_eq_zero Finset.univ _
      (fun i _ => ha i) hp
    have hi0 : ⇑f ∣[k] levelSixRep i = 0 := by
      ext τ
      simpa only [Function.comp_apply, ofComplex_apply, Pi.zero_apply] using hi τ τ.im_pos
    have hf0 := (slash_SL2_eq_zero_iff k (levelSixRep i) f).mp hi0
    exact ModularForm.ext (congrFun hf0)
  · rintro rfl
    apply ModularForm.ext
    intro τ
    simp

end DirichletL

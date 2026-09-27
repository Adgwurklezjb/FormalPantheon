import Arithmetic.LevelSixEtaWords
import Analysis.DedekindEtaScaling
import Analysis.LevelSixModularForms

/-!
The eta quotient in CDT v2 Section 11.1, equation `haupt`, is holomorphic
on the upper half-plane and invariant under Gamma0(6). Its normalization
agrees with the displayed Euler product. Cusp values and uniformization
require further arguments and are not asserted here.
-/

namespace DirichletL

open Complex Function.Periodic
open _root_.UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-- The eta quotient representing the level-six Hauptmodul. -/
noncomputable def hauptmodulEta (τ : ℂ) : ℂ :=
  dedekindEta τ ^ 4 * dedekindEta (6 * τ) ^ 8 /
    (dedekindEta (2 * τ) ^ 8 * dedekindEta (3 * τ) ^ 4)

/-- The positive-index Euler product in CDT's equation `haupt`. -/
noncomputable def hauptmodulProduct (q : ℂ) : ℂ :=
  q * qEulerProduct q ^ 4 * qEulerProduct (q ^ 6) ^ 8 /
    (qEulerProduct (q ^ 2) ^ 8 * qEulerProduct (q ^ 3) ^ 4)

theorem hauptmodulEta_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : hauptmodulEta τ ≠ 0 := by
  have h2 : 0 < (2 * τ).im := by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hτ
  have h3 : 0 < (3 * τ).im := by simpa using mul_pos (by norm_num : (0 : ℝ) < 3) hτ
  have h6 : 0 < (6 * τ).im := by simpa using mul_pos (by norm_num : (0 : ℝ) < 6) hτ
  exact div_ne_zero
    (mul_ne_zero (pow_ne_zero _ (dedekindEta_ne_zero hτ))
      (pow_ne_zero _ (dedekindEta_ne_zero h6)))
    (mul_ne_zero (pow_ne_zero _ (dedekindEta_ne_zero h2))
      (pow_ne_zero _ (dedekindEta_ne_zero h3)))

theorem differentiableOn_hauptmodulEta :
    DifferentiableOn ℂ hauptmodulEta {τ : ℂ | 0 < τ.im} := by
  apply ((differentiableOn_dedekindEta.pow 4).mul
    ((differentiableOn_dedekindEta_nat_mul 6 (by norm_num)).pow 8)).div
      (((differentiableOn_dedekindEta_nat_mul 2 (by norm_num)).pow 8).mul
        ((differentiableOn_dedekindEta_nat_mul 3 (by norm_num)).pow 4))
  intro τ hτ
  apply mul_ne_zero <;> apply pow_ne_zero <;> apply dedekindEta_ne_zero
  · simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hτ
  · simpa using mul_pos (by norm_num : (0 : ℝ) < 3) hτ

theorem mdifferentiable_hauptmodulEta :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => hauptmodulEta τ) := by
  apply UpperHalfPlane.mdifferentiable_iff.mpr
  apply differentiableOn_hauptmodulEta.congr
  intro τ hτ
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hτ, coe_mk_subtype]

theorem hauptmodulEta_eq_product (τ : ℂ) :
    hauptmodulEta τ = hauptmodulProduct (qParam 1 τ) := by
  have hq2 := qParam_one_nat_mul 2 τ
  have hq3 := qParam_one_nat_mul 3 τ
  have hq6 := qParam_one_nat_mul 6 τ
  simp only [Nat.cast_ofNat] at hq2 hq3 hq6
  simp only [hauptmodulEta, dedekindEta, mul_pow, hq2, hq3, hq6, hauptmodulProduct]
  have he : exp (π * I * τ / 12) ^ 4 * exp (π * I * (6 * τ) / 12) ^ 8 /
      (exp (π * I * (2 * τ) / 12) ^ 8 * exp (π * I * (3 * τ) / 12) ^ 4) =
        qParam 1 τ := by
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_nat_mul, ← exp_nat_mul,
      ← exp_add, ← exp_add, ← exp_sub]
    simp only [qParam, ofReal_one, div_one, Nat.cast_ofNat]
    congr 1
    ring
  calc
    _ = (exp (π * I * τ / 12) ^ 4 * exp (π * I * (6 * τ) / 12) ^ 8 /
        (exp (π * I * (2 * τ) / 12) ^ 8 * exp (π * I * (3 * τ) / 12) ^ 4)) *
          (qEulerProduct (qParam 1 τ) ^ 4 * qEulerProduct (qParam 1 τ ^ 6) ^ 8 /
            (qEulerProduct (qParam 1 τ ^ 2) ^ 8 * qEulerProduct (qParam 1 τ ^ 3) ^ 4)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [he]; ring

private theorem hauptmodulEta_generator_invariant (b : Bool) (i : Fin 12) (τ : ℍ) :
    hauptmodulEta ((levelSixEtaMatrix b i • τ : ℍ) : ℂ) = hauptmodulEta τ := by
  let γ := levelSixEtaMatrix b i
  let e (j : Fin 4) := modularWordExponent (levelSixEtaWord b i j)
  let D : ℂ := (γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)
  have hD : D ≠ 0 := denom_ne_zero γ τ
  have h (j : Fin 4) := dedekindEta_sq_nat_mul_smul (levelSixEtaScale j)
    (levelSixEtaScale_pos j) γ (levelSixEtaWord b i j) (levelSixEtaWord_matrix b i j) τ
  have h1 := h 0
  have h2 := h 1
  have h3 := h 2
  have h6 := h 3
  norm_num [levelSixEtaScale] at h1 h2 h3 h6
  change dedekindEta ((γ • τ : ℍ) : ℂ) ^ 2 =
    dedekindEtaRoot ^ e 0 * D * dedekindEta τ ^ 2 at h1
  change dedekindEta (2 * ((γ • τ : ℍ) : ℂ)) ^ 2 =
    dedekindEtaRoot ^ e 1 * D * dedekindEta (2 * τ) ^ 2 at h2
  change dedekindEta (3 * ((γ • τ : ℍ) : ℂ)) ^ 2 =
    dedekindEtaRoot ^ e 2 * D * dedekindEta (3 * τ) ^ 2 at h3
  change dedekindEta (6 * ((γ • τ : ℍ) : ℂ)) ^ 2 =
    dedekindEtaRoot ^ e 3 * D * dedekindEta (6 * τ) ^ 2 at h6
  have hr : dedekindEtaRoot ^ (2 * e 0 - 4 * e 1 - 2 * e 2 + 4 * e 3) = 1 :=
    dedekindEtaRoot_zpow_eq_one_of_dvd (levelSixEtaWord_exponent b i)
  rw [show 2 * e 0 - 4 * e 1 - 2 * e 2 + 4 * e 3 =
    (e 0 * 2 + e 3 * 4) - (e 1 * 4 + e 2 * 2) by ring,
    zpow_sub₀ dedekindEtaRoot_ne_zero,
    div_eq_one_iff_eq (zpow_ne_zero _ dedekindEtaRoot_ne_zero)] at hr
  have hroot : (dedekindEtaRoot ^ e 0) ^ 2 * (dedekindEtaRoot ^ e 3) ^ 4 =
      (dedekindEtaRoot ^ e 1) ^ 4 * (dedekindEtaRoot ^ e 2) ^ 2 := by
    simpa only [zpow_add₀ dedekindEtaRoot_ne_zero, zpow_mul, zpow_ofNat] using hr
  rw [hauptmodulEta]
  simp only [show ∀ z : ℂ, z ^ 4 = (z ^ 2) ^ 2 from fun z => pow_mul z 2 2,
    show ∀ z : ℂ, z ^ 8 = (z ^ 2) ^ 4 from fun z => pow_mul z 2 4]
  rw [h1, h2, h3, h6]
  simp only [mul_pow]
  have hroot0 : (dedekindEtaRoot ^ e 1) ^ 4 * (dedekindEtaRoot ^ e 2) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (zpow_ne_zero _ dedekindEtaRoot_ne_zero))
      (pow_ne_zero _ (zpow_ne_zero _ dedekindEtaRoot_ne_zero))
  calc
    _ = ((dedekindEtaRoot ^ e 0) ^ 2 * (dedekindEtaRoot ^ e 3) ^ 4) /
        ((dedekindEtaRoot ^ e 1) ^ 4 * (dedekindEtaRoot ^ e 2) ^ 2) *
          (D ^ 6 / D ^ 6) * hauptmodulEta τ := by
      simp only [hauptmodulEta, div_eq_mul_inv, mul_inv_rev, pow_mul, ← inv_pow]
      ring
    _ = _ := by rw [hroot, div_self hroot0, div_self (pow_ne_zero _ hD), one_mul, one_mul]

theorem hauptmodulEta_slash (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 6) :
    (fun τ : ℍ => hauptmodulEta τ) ∣[(0 : ℤ)] γ = (fun τ : ℍ => hauptmodulEta τ) := by
  apply slashInvariant_levelSix_of_rep_mul_S_of_rep_mul_T _ _ ?_ ?_ γ hγ
  · intro i
    ext τ
    apply (ModularForm.slash_action_eq'_iff _ _ _ _).mpr
    simpa only [zpow_zero, one_mul] using hauptmodulEta_generator_invariant false i τ
  · intro i
    ext τ
    apply (ModularForm.slash_action_eq'_iff _ _ _ _).mpr
    simpa only [zpow_zero, one_mul] using hauptmodulEta_generator_invariant true i τ

theorem hauptmodulEta_invariant (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 6)
    (τ : ℍ) : hauptmodulEta ((γ • τ : ℍ) : ℂ) = hauptmodulEta τ := by
  have h := congrFun (hauptmodulEta_slash γ hγ) τ
  simpa only [zpow_zero, one_mul] using (ModularForm.slash_action_eq'_iff _ _ _ _).mp h

theorem hauptmodulProduct_qParam_invariant (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 6) (τ : ℍ) :
    hauptmodulProduct (qParam 1 ((γ • τ : ℍ) : ℂ)) = hauptmodulProduct (qParam 1 τ) := by
  rw [← hauptmodulEta_eq_product, ← hauptmodulEta_eq_product]
  exact hauptmodulEta_invariant γ hγ τ

end DirichletL

import Arithmetic.LevelSixEtaWords
import Analysis.DedekindEtaScaling
import Analysis.LevelSixModularForms

/-!
Four-factor eta-square quotients for the case C products in Zagier (2009),
Section 5, PDF page 8, and CDT v2 Section 11.1. Integer exponents retain
reciprocal factors. Cusp bounds are a separate input to modularity.
-/

namespace DirichletL

open Complex
open _root_.UpperHalfPlane hiding I
open scoped Manifold MatrixGroups ModularForm

/-- Eta squared at scales 1,2,3,6 with specified integer exponents. -/
noncomputable def levelSixEtaQuotient (m : Fin 4 → ℤ) (τ : ℂ) : ℂ :=
  ∏ j, (dedekindEta ((levelSixEtaScale j : ℂ) * τ) ^ 2) ^ m j

theorem levelSixEtaQuotient_ne_zero (m : Fin 4 → ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    levelSixEtaQuotient m τ ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply zpow_ne_zero
  apply pow_ne_zero
  apply dedekindEta_ne_zero
  simpa using mul_pos
    (show (0 : ℝ) < levelSixEtaScale j by exact_mod_cast levelSixEtaScale_pos j) hτ

theorem differentiableOn_levelSixEtaQuotient (m : Fin 4 → ℤ) :
    DifferentiableOn ℂ (levelSixEtaQuotient m) {τ : ℂ | 0 < τ.im} := by
  apply DifferentiableOn.fun_finset_prod
  intro j _
  apply ((differentiableOn_dedekindEta_nat_mul _ (levelSixEtaScale_pos j)).pow 2).zpow
  left
  intro τ hτ
  apply pow_ne_zero
  apply dedekindEta_ne_zero
  simpa using mul_pos
    (show (0 : ℝ) < levelSixEtaScale j by exact_mod_cast levelSixEtaScale_pos j) hτ

theorem mdifferentiable_levelSixEtaQuotient (m : Fin 4 → ℤ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => levelSixEtaQuotient m τ) := by
  apply UpperHalfPlane.mdifferentiable_iff.mpr
  apply (differentiableOn_levelSixEtaQuotient m).congr
  intro τ hτ
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hτ, coe_mk_subtype]

theorem levelSixEtaQuotient_add (m n : Fin 4 → ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    levelSixEtaQuotient (m + n) τ = levelSixEtaQuotient m τ * levelSixEtaQuotient n τ := by
  unfold levelSixEtaQuotient
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have h : dedekindEta ((levelSixEtaScale j : ℂ) * τ) ≠ 0 := by
    apply dedekindEta_ne_zero
    simpa using mul_pos
      (show (0 : ℝ) < levelSixEtaScale j by exact_mod_cast levelSixEtaScale_pos j) hτ
  exact zpow_add₀ (pow_ne_zero 2 h) _ _

theorem levelSixEtaQuotient_nat_mul (m : Fin 4 → ℤ) (r : ℕ) (τ : ℂ) :
    levelSixEtaQuotient (fun j => (r : ℤ) * m j) τ = levelSixEtaQuotient m τ ^ r := by
  unfold levelSixEtaQuotient
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  dsimp only
  rw [mul_comm (r : ℤ), zpow_mul, zpow_natCast]

theorem levelSixEtaQuotient_generator_apply (m : Fin 4 → ℤ) (b : Bool) (i : Fin 12)
    (τ : ℍ) :
    levelSixEtaQuotient m ((levelSixEtaMatrix b i • τ : ℍ) : ℂ) =
      dedekindEtaRoot ^ (∑ j, m j * modularWordExponent (levelSixEtaWord b i j)) *
        (((levelSixEtaMatrix b i) 1 0 : ℂ) * τ + ((levelSixEtaMatrix b i) 1 1 : ℂ)) ^
          (∑ j, m j) * levelSixEtaQuotient m τ := by
  let γ := levelSixEtaMatrix b i
  let D : ℂ := (γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)
  have hD : D ≠ 0 := denom_ne_zero γ τ
  have h (j : Fin 4) := dedekindEta_sq_nat_mul_smul (levelSixEtaScale j)
    (levelSixEtaScale_pos j) γ (levelSixEtaWord b i j) (levelSixEtaWord_matrix b i j) τ
  have he (j : Fin 4) :
      (dedekindEtaRoot ^ modularWordExponent (levelSixEtaWord b i j)) ^ m j =
        dedekindEtaRoot ^ (m j * modularWordExponent (levelSixEtaWord b i j)) := by
    rw [mul_comm (m j), zpow_mul]
  have hr : (∏ j, (dedekindEtaRoot ^ modularWordExponent (levelSixEtaWord b i j)) ^ m j) =
      dedekindEtaRoot ^ (∑ j, m j * modularWordExponent (levelSixEtaWord b i j)) := by
    simp only [he, Fin.prod_univ_four, Fin.sum_univ_four, zpow_add₀ dedekindEtaRoot_ne_zero]
  have hd : (∏ j, D ^ m j) = D ^ (∑ j, m j) := by
    simp only [Fin.prod_univ_four, Fin.sum_univ_four, zpow_add₀ hD]
  change levelSixEtaQuotient m ((γ • τ : ℍ) : ℂ) = _ * D ^ (∑ j, m j) * _
  simp only [levelSixEtaQuotient, h, mul_zpow, Finset.prod_mul_distrib]
  rw [hr, hd]

theorem levelSixEtaQuotient_slash (m : Fin 4 → ℤ)
    (hm : ∀ b i, 12 ∣ ∑ j, m j * modularWordExponent (levelSixEtaWord b i j))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 6) :
    (fun τ : ℍ => levelSixEtaQuotient m τ) ∣[∑ j, m j] γ =
      (fun τ : ℍ => levelSixEtaQuotient m τ) := by
  have hgen (b : Bool) (i : Fin 12) :
      (fun τ : ℍ => levelSixEtaQuotient m τ) ∣[∑ j, m j] levelSixEtaMatrix b i =
        (fun τ : ℍ => levelSixEtaQuotient m τ) := by
    have he : (fun τ : ℍ => levelSixEtaQuotient m τ) ∣[∑ j, m j] levelSixEtaMatrix b i =
        (1 : ℂ) • (fun τ : ℍ => levelSixEtaQuotient m τ) := by
      apply (slash_eq_smul_iff _ _ _ _).mpr
      intro τ
      rw [levelSixEtaQuotient_generator_apply,
        dedekindEtaRoot_zpow_eq_one_of_dvd (hm b i)]
    simpa only [one_smul] using he
  apply slashInvariant_levelSix_of_rep_mul_S_of_rep_mul_T _ _ ?_ ?_ γ hγ
  · intro i
    simpa only [levelSixEtaMatrix] using hgen false i
  · intro i
    simpa only [levelSixEtaMatrix] using hgen true i

end DirichletL

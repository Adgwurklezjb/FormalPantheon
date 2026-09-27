import Arithmetic.LevelSixEtaCusps
import Analysis.DedekindEtaCuspBounds
import Analysis.LevelSixEtaQuotient

/-!
Cusp transformations and modular-form construction for the level-six eta
quotients in Zagier (2009), Section 5, case C, and CDT v2 Section 11.1.
The finite rational slope conditions imply actual analytic cusp bounds.
-/

namespace DirichletL

open Complex
open _root_.UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm

/-- The constant multiplier in a certified affine cusp transformation. -/
noncomputable def levelSixEtaCuspFactor (m : Fin 4 → ℤ) (i : Fin 12) : ℂ :=
  ∏ j, (dedekindEtaRoot ^ modularWordExponent (levelSixEtaCuspData i j).word /
    ((levelSixEtaCuspData i j).denominator : ℂ)) ^ m j

theorem levelSixEtaQuotient_slash_rep (m : Fin 4 → ℤ) (i : Fin 12) :
    (fun τ : ℍ => levelSixEtaQuotient m τ) ∣[∑ j, m j] levelSixRep i =
      fun τ : ℍ => levelSixEtaCuspFactor m i *
        ∏ j, (dedekindEta ((((levelSixEtaCuspData i j).numerator : ℂ) * τ +
          ((levelSixEtaCuspData i j).offset : ℂ)) /
            ((levelSixEtaCuspData i j).denominator : ℂ)) ^ 2) ^ m j := by
  ext τ
  let D : ℂ := ((levelSixRep i) 1 0 : ℂ) * τ + ((levelSixRep i) 1 1 : ℂ)
  have hD : D ≠ 0 := denom_ne_zero (levelSixRep i) τ
  simp only [ModularForm.SL_slash_def, UpperHalfPlane.denom, zpow_neg]
  change levelSixEtaQuotient m ((levelSixRep i • τ : ℍ) : ℂ) *
    (D ^ (∑ j, m j))⁻¹ = _
  rw [mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ hD)]
  have h (j : Fin 4) :
      dedekindEta ((levelSixEtaScale j : ℂ) * ((levelSixRep i • τ : ℍ) : ℂ)) ^ 2 =
        (dedekindEtaRoot ^ modularWordExponent (levelSixEtaCuspData i j).word /
          ((levelSixEtaCuspData i j).denominator : ℂ)) * D *
            dedekindEta ((((levelSixEtaCuspData i j).numerator : ℂ) * τ +
              ((levelSixEtaCuspData i j).offset : ℂ)) /
                ((levelSixEtaCuspData i j).denominator : ℂ)) ^ 2 := by
    have he := dedekindEta_sq_affine_smul (levelSixEtaScale j)
      (levelSixEtaCuspData i j).numerator (levelSixEtaCuspData i j).denominator
      (levelSixEtaCuspData_numerator_pos i j) (levelSixEtaCuspData_denominator_pos i j)
      (levelSixEtaCuspData i j).offset (levelSixRep i) (levelSixEtaCuspData i j).word
      (levelSixEtaCuspData_matrix i j) τ
    simpa only [D, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using he
  have hd : (∏ j, D ^ m j) = D ^ (∑ j, m j) := by
    simp only [Fin.prod_univ_four, Fin.sum_univ_four, zpow_add₀ hD]
  simp only [levelSixEtaQuotient, h, mul_zpow, Finset.prod_mul_distrib]
  rw [hd]
  simp only [levelSixEtaCuspFactor, mul_assoc, mul_left_comm, mul_comm]

theorem isBoundedAtImInfty_levelSixEtaQuotient_slash_rep (m : Fin 4 → ℤ) (i : Fin 12)
    (hs : (0 : ℚ) ≤ ∑ j, (m j : ℚ) * ((levelSixEtaCuspData i j).numerator : ℚ) /
      ((levelSixEtaCuspData i j).denominator : ℚ)) :
    IsBoundedAtImInfty ((fun τ : ℍ => levelSixEtaQuotient m τ) ∣[∑ j, m j] levelSixRep i) := by
  rw [levelSixEtaQuotient_slash_rep]
  let u (j : Fin 4) : ℝ := (levelSixEtaCuspData i j).numerator /
    ((levelSixEtaCuspData i j).denominator : ℝ)
  let v (j : Fin 4) : ℝ := (levelSixEtaCuspData i j).offset /
    ((levelSixEtaCuspData i j).denominator : ℝ)
  have hu (j : Fin 4) : 0 < u j := div_pos
    (by exact_mod_cast levelSixEtaCuspData_numerator_pos i j)
    (by exact_mod_cast levelSixEtaCuspData_denominator_pos i j)
  have hsR : 0 ≤ ∑ j, (m j : ℝ) * u j := by
    have hs' : (0 : ℝ) ≤ ∑ j, (m j : ℝ) * ((levelSixEtaCuspData i j).numerator : ℝ) /
        ((levelSixEtaCuspData i j).denominator : ℝ) := by exact_mod_cast hs
    simpa only [u, mul_div_assoc] using hs'
  have hb := isBoundedAtImInfty_dedekindEta_sq_affine_prod m u v hu hsR
  have hb' : IsBoundedAtImInfty
      (fun τ : ℍ => ∏ j, (dedekindEta ((((levelSixEtaCuspData i j).numerator : ℂ) * τ +
        ((levelSixEtaCuspData i j).offset : ℂ)) /
          ((levelSixEtaCuspData i j).denominator : ℂ)) ^ 2) ^ m j) := by
    convert hb using 1
    ext τ
    apply Finset.prod_congr rfl
    intro j _
    apply congrArg (fun z : ℂ => (dedekindEta z ^ 2) ^ m j)
    dsimp only [u, v]
    push_cast
    ring
  exact Filter.BoundedAtFilter.mul
    (Filter.const_boundedAtFilter atImInfty (levelSixEtaCuspFactor m i)) hb'

/-- A level-six eta quotient from its exact multipliers and nonnegative cusp slopes. -/
noncomputable def levelSixEtaQuotientModularForm (m : Fin 4 → ℤ)
    (hm : ∀ b i, 12 ∣ ∑ j, m j * modularWordExponent (levelSixEtaWord b i j))
    (hs : ∀ i, (0 : ℚ) ≤ ∑ j, (m j : ℚ) * ((levelSixEtaCuspData i j).numerator : ℚ) /
      ((levelSixEtaCuspData i j).denominator : ℚ)) :
    ModularForm (CongruenceSubgroup.Gamma0 6) (∑ j, m j) :=
  levelSixModularForm _ (fun τ : ℍ => levelSixEtaQuotient m τ)
    (fun i => levelSixEtaQuotient_slash m hm _ (levelSixRep_mul_S_mem i))
    (fun i => levelSixEtaQuotient_slash m hm _ (levelSixRep_mul_T_mem i))
    (mdifferentiable_levelSixEtaQuotient m)
    (fun i => isBoundedAtImInfty_levelSixEtaQuotient_slash_rep m i (hs i))

@[simp] theorem levelSixEtaQuotientModularForm_apply (m : Fin 4 → ℤ) (hm hs) (τ : ℍ) :
    levelSixEtaQuotientModularForm m hm hs τ = levelSixEtaQuotient m τ := rfl

end DirichletL

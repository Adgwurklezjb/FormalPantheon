import Analysis.DedekindEtaLogDifferential
import Analysis.LevelSixEtaLogDerivative

/-!
Weight-four cusp bounds for the second identity of Zagier (2009),
Section 5, equation (7), using the certified affine eta transformations.
-/

namespace DirichletL

open Complex Filter
open _root_.UpperHalfPlane hiding I
open scoped Topology MatrixGroups ModularForm

theorem modularLogDerivCorrection_levelSixEtaQuotient_slash_rep (m : Fin 4 → ℤ)
    (hm : ∑ j, m j = 2) (i : Fin 12) :
    (fun τ : ℍ => modularLogDerivCorrection (levelSixEtaQuotient m) τ)
      ∣[(4 : ℤ)] levelSixRep i =
      fun τ : ℍ => modularLogDerivCorrection (fun z : ℂ =>
        ∏ j, (dedekindEta ((((levelSixEtaCuspData i j).numerator : ℂ) * z +
          ((levelSixEtaCuspData i j).offset : ℂ)) /
            ((levelSixEtaCuspData i j).denominator : ℂ)) ^ 2) ^ m j) τ := by
  let P (z : ℂ) : ℂ := ∏ j, (dedekindEta
    ((((levelSixEtaCuspData i j).numerator : ℂ) * z +
      ((levelSixEtaCuspData i j).offset : ℂ)) /
        ((levelSixEtaCuspData i j).denominator : ℂ)) ^ 2) ^ m j
  let u (j : Fin 4) : ℝ := (levelSixEtaCuspData i j).numerator /
    ((levelSixEtaCuspData i j).denominator : ℝ)
  let v (j : Fin 4) : ℝ := (levelSixEtaCuspData i j).offset /
    ((levelSixEtaCuspData i j).denominator : ℝ)
  have hu (j : Fin 4) : 0 < u j := div_pos
    (by exact_mod_cast levelSixEtaCuspData_numerator_pos i j)
    (by exact_mod_cast levelSixEtaCuspData_denominator_pos i j)
  have he : P = fun z : ℂ =>
      ∏ j, (dedekindEta ((u j : ℂ) * z + (v j : ℂ)) ^ 2) ^ m j := by
    ext z
    apply Finset.prod_congr rfl
    intro j _
    apply congrArg (fun w : ℂ => (dedekindEta w ^ 2) ^ m j)
    dsimp only [u, v]
    push_cast
    ring
  have hP : DifferentiableOn ℂ P {z | 0 < z.im} := by
    rw [he]
    exact differentiableOn_dedekindEta_sq_affine_prod m u v hu
  have hP0 (z : ℂ) (hz : 0 < z.im) : P z ≠ 0 := by
    rw [he]
    exact dedekindEta_sq_affine_prod_ne_zero m u v hu hz
  have hc := levelSixEtaCuspFactor_ne_zero m i
  have hrel (τ : ℍ) : levelSixEtaQuotient m ((levelSixRep i • τ : ℍ) : ℂ) =
      (((levelSixRep i) 1 0 : ℂ) * τ + ((levelSixRep i) 1 1 : ℂ)) ^ 2 *
        (levelSixEtaCuspFactor m i * P τ) := by
    have h := congrFun (levelSixEtaQuotient_slash_rep m i) τ
    rw [hm] at h
    simp only [ModularForm.SL_slash_def, UpperHalfPlane.denom,
      zpow_neg, zpow_ofNat] at h
    change levelSixEtaQuotient m ((levelSixRep i • τ : ℍ) : ℂ) *
      ((((levelSixRep i) 1 0 : ℂ) * τ + ((levelSixRep i) 1 1 : ℂ)) ^ 2)⁻¹ =
        levelSixEtaCuspFactor m i * P τ at h
    exact ((mul_inv_eq_iff_eq_mul₀ (pow_ne_zero 2 (denom_ne_zero (levelSixRep i) τ))).mp h).trans
      (mul_comm _ _)
  have h := modularLogDerivCorrection_slash_of_weightTwoRelation
    (differentiableOn_levelSixEtaQuotient m) (hP.const_mul (levelSixEtaCuspFactor m i))
    (fun _ hz => levelSixEtaQuotient_ne_zero m hz) (fun z hz => mul_ne_zero hc (hP0 z hz))
    (levelSixRep i) hrel
  simpa only [modularLogDerivCorrection_const_mul P hc] using h

theorem isBoundedAtImInfty_modularLogDerivCorrection_levelSixEtaQuotient_slash_rep
    (m : Fin 4 → ℤ) (hm : ∑ j, m j = 2) (i : Fin 12) :
    IsBoundedAtImInfty
      ((fun τ : ℍ => modularLogDerivCorrection (levelSixEtaQuotient m) τ)
        ∣[(4 : ℤ)] levelSixRep i) := by
  rw [modularLogDerivCorrection_levelSixEtaQuotient_slash_rep m hm]
  let u (j : Fin 4) : ℝ := (levelSixEtaCuspData i j).numerator /
    ((levelSixEtaCuspData i j).denominator : ℝ)
  let v (j : Fin 4) : ℝ := (levelSixEtaCuspData i j).offset /
    ((levelSixEtaCuspData i j).denominator : ℝ)
  have hu (j : Fin 4) : 0 < u j := div_pos
    (by exact_mod_cast levelSixEtaCuspData_numerator_pos i j)
    (by exact_mod_cast levelSixEtaCuspData_denominator_pos i j)
  have he : (fun z : ℂ => ∏ j, (dedekindEta
      ((((levelSixEtaCuspData i j).numerator : ℂ) * z +
        ((levelSixEtaCuspData i j).offset : ℂ)) /
          ((levelSixEtaCuspData i j).denominator : ℂ)) ^ 2) ^ m j) =
      fun z : ℂ => ∏ j, (dedekindEta ((u j : ℂ) * z + (v j : ℂ)) ^ 2) ^ m j := by
    ext z
    apply Finset.prod_congr rfl
    intro j _
    apply congrArg (fun w : ℂ => (dedekindEta w ^ 2) ^ m j)
    dsimp only [u, v]
    push_cast
    ring
  rw [he]
  exact (tendsto_modularLogDerivCorrection_dedekindEta_sq_affine_prod m u v hu).isBigO_one ℝ

end DirichletL

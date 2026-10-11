import Analysis.LevelSixEtaLogDifferential
import Analysis.ZagierEtaModular

/-!
The actual weight-four difference for Zagier (2009), Section 5,
equation (7), in the case-C normalization of CDT v2 Section 11.1.
Its vanishing requires a subsequent exact coefficient comparison.
-/

namespace DirichletL

open Complex Filter
open _root_.UpperHalfPlane hiding I
open scoped Topology MatrixGroups ModularForm

theorem modularLogDerivCorrection_zagierEtaSquare_slash (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 6) :
    (fun τ : ℍ => modularLogDerivCorrection zagierEtaSquare τ) ∣[(4 : ℤ)] γ =
      fun τ : ℍ => modularLogDerivCorrection zagierEtaSquare τ := by
  apply modularLogDerivCorrection_slash_of_weightTwoRelation
    (differentiableOn_levelSixEtaQuotient (zagierEtaExponents 0))
    (differentiableOn_levelSixEtaQuotient (zagierEtaExponents 0))
    (fun _ hz => levelSixEtaQuotient_ne_zero (zagierEtaExponents 0) hz)
    (fun _ hz => levelSixEtaQuotient_ne_zero (zagierEtaExponents 0) hz) γ
  intro τ
  simpa only [zagierEtaWeightTwoForm_apply, zagierEtaSquare, zpow_ofNat] using
    SlashInvariantForm.slash_action_eqn' (zagierEtaWeightTwoForm 0)
      (show (Matrix.SpecialLinearGroup.mapGL ℝ) γ ∈
        Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 6) from
        ⟨γ, hγ, rfl⟩) τ

/-- The logarithmic differential of the actual case-C eta square. -/
noncomputable def zagierEtaLogDifferentialForm :
    ModularForm (CongruenceSubgroup.Gamma0 6) 4 :=
  levelSixModularForm _ (fun τ : ℍ => modularLogDerivCorrection zagierEtaSquare τ)
    (fun i => modularLogDerivCorrection_zagierEtaSquare_slash _ (levelSixRep_mul_S_mem i))
    (fun i => modularLogDerivCorrection_zagierEtaSquare_slash _ (levelSixRep_mul_T_mem i))
    (mdifferentiable_modularLogDerivCorrection
      (differentiableOn_levelSixEtaQuotient (zagierEtaExponents 0))
      (fun _ hz => levelSixEtaQuotient_ne_zero (zagierEtaExponents 0) hz))
    (fun i => isBoundedAtImInfty_modularLogDerivCorrection_levelSixEtaQuotient_slash_rep
      (zagierEtaExponents 0) (sum_zagierEtaExponents 0) i)

@[simp] theorem zagierEtaLogDifferentialForm_apply (τ : ℍ) :
    zagierEtaLogDifferentialForm τ = modularLogDerivCorrection zagierEtaSquare τ := rfl

theorem tendsto_modularLogDerivCorrection_zagierEtaSquare :
    Tendsto (fun τ : ℍ => modularLogDerivCorrection zagierEtaSquare τ) atImInfty (𝓝 0) := by
  have ht := tendsto_modularLogDerivCorrection_dedekindEta_sq_affine_prod
    (zagierEtaExponents 0) (fun j => (levelSixEtaScale j : ℝ)) (fun _ => 0)
    (fun j => by
      change (0 : ℝ) < levelSixEtaScale j
      exact_mod_cast levelSixEtaScale_pos j)
  have he : (fun z : ℂ => ∏ j,
      (dedekindEta (((levelSixEtaScale j : ℝ) : ℂ) * z + ((0 : ℝ) : ℂ)) ^ 2) ^
        zagierEtaExponents 0 j) = zagierEtaSquare := by
    ext z
    simp only [ofReal_natCast, ofReal_zero, add_zero]
    rfl
  rw [he] at ht
  norm_num [Fin.sum_univ_four, zagierEtaExponents, levelSixEtaScale,
    Matrix.cons_val_two, Matrix.cons_val_three] at ht
  exact ht

/-- The weight-four difference for the second case-C differential identity. -/
noncomputable def zagierSecondDerivativeDifferenceForm :
    ModularForm (CongruenceSubgroup.Gamma0 6) 4 :=
  zagierEtaLogDifferentialForm +
    12 • (zagierEtaWeightTwoForm 0).mul (zagierEtaWeightTwoForm 1) -
    156 • (zagierEtaWeightTwoForm 1).mul (zagierEtaWeightTwoForm 1) +
    468 • (zagierEtaWeightTwoForm 1).mul (zagierEtaWeightTwoForm 2) -
    324 • (zagierEtaWeightTwoForm 2).mul (zagierEtaWeightTwoForm 2)

@[simp] theorem zagierSecondDerivativeDifferenceForm_apply (τ : ℍ) :
    zagierSecondDerivativeDifferenceForm τ = modularLogDerivCorrection zagierEtaSquare τ -
      4 * hauptmodulEta τ * (1 - 10 * hauptmodulEta τ + 9 * hauptmodulEta τ ^ 2) *
        (9 * hauptmodulEta τ - 3) * zagierEtaSquare τ ^ 2 := by
  simp only [zagierSecondDerivativeDifferenceForm, ModularForm.sub_apply, ModularForm.add_apply,
    ModularForm.smul_apply, ModularForm.mul_coe, Pi.mul_apply,
    zagierEtaLogDifferentialForm_apply, zagierEtaWeightTwoForm_eq]
  norm_num only [nsmul_eq_mul, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, one_mul]
  ring

end DirichletL

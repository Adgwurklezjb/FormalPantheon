import Arithmetic.ZagierEtaExponents
import Analysis.LevelSixEtaCuspBounds
import Analysis.HauptmodulModular

/-!
The three actual weight-two modular forms f^2, x*f^2, and x^2*f^2 from
Zagier (2009), Section 5, case C, PDF page 8, and CDT v2 Section 11.1.
Their identification with binomial generating functions is a later step.
-/

namespace DirichletL

open Complex
open _root_.UpperHalfPlane hiding I

/-- The square of the case C weight-one eta product. -/
noncomputable def zagierEtaSquare (τ : ℂ) : ℂ :=
  levelSixEtaQuotient (zagierEtaExponents 0) τ

theorem zagierEtaSquare_eq (τ : ℂ) :
    zagierEtaSquare τ =
      (dedekindEta (2 * τ) ^ 6 * dedekindEta (3 * τ) /
        (dedekindEta τ ^ 3 * dedekindEta (6 * τ) ^ 2)) ^ 2 := by
  norm_num [zagierEtaSquare, levelSixEtaQuotient, Fin.prod_univ_four,
    zagierEtaExponents, levelSixEtaScale, Matrix.cons_val_two, Matrix.cons_val_three,
    div_pow, mul_pow, div_eq_mul_inv, mul_inv_rev, ← inv_pow]
  simp only [zpow_ofNat, ← inv_pow]
  ring

theorem levelSixEtaQuotient_eq_hauptmodulEta (τ : ℂ) :
    levelSixEtaQuotient ![2, -4, -2, 4] τ = hauptmodulEta τ := by
  norm_num [levelSixEtaQuotient, Fin.prod_univ_four, levelSixEtaScale,
    Matrix.cons_val_two, Matrix.cons_val_three, hauptmodulEta,
    div_eq_mul_inv, mul_inv_rev, ← inv_pow]
  simp only [zpow_ofNat, ← inv_pow]
  ring

/-- The case C eta products with all modularity hypotheses discharged. -/
noncomputable def zagierEtaWeightTwoForm (r : Fin 3) :
    ModularForm (CongruenceSubgroup.Gamma0 6) 2 :=
  ModularForm.mcast (sum_zagierEtaExponents r)
    (levelSixEtaQuotientModularForm (zagierEtaExponents r)
      (zagierEtaExponents_generator r) (zagierEtaExponents_cusp_nonneg r))

@[simp] theorem zagierEtaWeightTwoForm_apply (r : Fin 3) (τ : ℍ) :
    zagierEtaWeightTwoForm r τ = levelSixEtaQuotient (zagierEtaExponents r) τ := rfl

theorem zagierEtaWeightTwoForm_eq (r : Fin 3) (τ : ℍ) :
    zagierEtaWeightTwoForm r τ = hauptmodulEta τ ^ r.val * zagierEtaSquare τ := by
  have hm : zagierEtaExponents r = zagierEtaExponents 0 +
      (fun j => (r.val : ℤ) * (![2, -4, -2, 4] : Fin 4 → ℤ) j) := by
    ext j
    exact zagierEtaExponents_eq r j
  rw [zagierEtaWeightTwoForm_apply, hm, levelSixEtaQuotient_add _ _ τ.im_pos,
    levelSixEtaQuotient_nat_mul, levelSixEtaQuotient_eq_hauptmodulEta, mul_comm]
  rfl

end DirichletL

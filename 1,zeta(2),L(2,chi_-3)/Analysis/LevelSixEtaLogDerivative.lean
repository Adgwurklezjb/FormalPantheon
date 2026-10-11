import Analysis.DedekindEtaLogDerivative
import Analysis.LevelSixEtaCuspBounds

/-!
Cusp bounds for weight-zero eta logarithmic derivatives in Zagier (2009),
Section 5, equation (7), and CDT v2 Section 11.1. A pole of the original
eta quotient does not prevent its logarithmic derivative from being bounded.
-/

namespace DirichletL

open Complex Filter
open _root_.UpperHalfPlane hiding I
open scoped Topology MatrixGroups ModularForm Real

theorem levelSixEtaCuspFactor_ne_zero (m : Fin 4 → ℤ) (i : Fin 12) :
    levelSixEtaCuspFactor m i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply zpow_ne_zero
  apply div_ne_zero (zpow_ne_zero _ dedekindEtaRoot_ne_zero)
  exact_mod_cast (levelSixEtaCuspData_denominator_pos i j).ne'

theorem modularLogDeriv_levelSixEtaQuotient_slash_rep (m : Fin 4 → ℤ)
    (hm : ∑ j, m j = 0) (i : Fin 12) :
    (fun τ : ℍ => modularLogDeriv (levelSixEtaQuotient m) τ) ∣[(2 : ℤ)] levelSixRep i =
      fun τ : ℍ => modularLogDeriv (fun z : ℂ =>
        ∏ j, (dedekindEta ((((levelSixEtaCuspData i j).numerator : ℂ) * z +
          ((levelSixEtaCuspData i j).offset : ℂ)) /
            ((levelSixEtaCuspData i j).denominator : ℂ)) ^ 2) ^ m j) τ := by
  rw [modularLogDeriv_slash_SL2 (differentiableOn_levelSixEtaQuotient m)]
  ext τ
  apply congrArg (fun w : ℂ => w / (2 * π * I))
  let P (z : ℂ) : ℂ := ∏ j, (dedekindEta
    ((((levelSixEtaCuspData i j).numerator : ℂ) * z +
      ((levelSixEtaCuspData i j).offset : ℂ)) /
        ((levelSixEtaCuspData i j).denominator : ℂ)) ^ 2) ^ m j
  calc
    _ = logDeriv (fun z : ℂ => levelSixEtaCuspFactor m i * P z) τ := by
      apply logDeriv_eq_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos]
        with z hz
      have he := congrFun (levelSixEtaQuotient_slash_rep m i) ⟨z, hz⟩
      rw [hm] at he
      simpa only [ModularForm.SL_slash_def, mul_one, neg_zero, zpow_zero,
        ofComplex_apply_of_im_pos hz, coe_mk_subtype, P] using he
    _ = _ := logDeriv_const_mul _ _ (levelSixEtaCuspFactor_ne_zero m i)

theorem isBoundedAtImInfty_modularLogDeriv_levelSixEtaQuotient_slash_rep
    (m : Fin 4 → ℤ) (hm : ∑ j, m j = 0) (i : Fin 12) :
    IsBoundedAtImInfty
      ((fun τ : ℍ => modularLogDeriv (levelSixEtaQuotient m) τ) ∣[(2 : ℤ)] levelSixRep i) := by
  rw [modularLogDeriv_levelSixEtaQuotient_slash_rep m hm]
  let u (j : Fin 4) : ℝ := (levelSixEtaCuspData i j).numerator /
    ((levelSixEtaCuspData i j).denominator : ℝ)
  let v (j : Fin 4) : ℝ := (levelSixEtaCuspData i j).offset /
    ((levelSixEtaCuspData i j).denominator : ℝ)
  have hu (j : Fin 4) : 0 < u j := div_pos
    (by exact_mod_cast levelSixEtaCuspData_numerator_pos i j)
    (by exact_mod_cast levelSixEtaCuspData_denominator_pos i j)
  have ht := tendsto_modularLogDeriv_dedekindEta_sq_affine_prod m u v hu
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
  exact ht.isBigO_one ℝ

end DirichletL

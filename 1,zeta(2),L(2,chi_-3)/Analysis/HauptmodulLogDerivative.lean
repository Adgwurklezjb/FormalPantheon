import Analysis.LevelSixEtaLogDerivative
import Analysis.ZagierEtaModular

/-!
The normalized logarithmic derivative of CDT v2 Section 11.1's Hauptmodul
as an actual weight-two form. This is the left side of Zagier (2009),
Section 5, equation (7), after division by the nonvanishing Hauptmodul.
-/

namespace DirichletL

open Complex Filter
open _root_.UpperHalfPlane hiding I
open scoped Topology

/-- The actual Hauptmodul logarithmic derivative, including all cusp bounds. -/
noncomputable def hauptmodulLogDerivativeForm :
    ModularForm (CongruenceSubgroup.Gamma0 6) 2 :=
  levelSixModularForm _ (fun τ : ℍ => modularLogDeriv hauptmodulEta τ)
    (fun i => modularLogDeriv_slash_of_invariant differentiableOn_hauptmodulEta _
      (hauptmodulEta_invariant _ (levelSixRep_mul_S_mem i)))
    (fun i => modularLogDeriv_slash_of_invariant differentiableOn_hauptmodulEta _
      (hauptmodulEta_invariant _ (levelSixRep_mul_T_mem i)))
    (mdifferentiable_modularLogDeriv differentiableOn_hauptmodulEta
      (fun _ hz => hauptmodulEta_ne_zero hz))
    (fun i => by
      have hm : ∑ j, (![2, -4, -2, 4] : Fin 4 → ℤ) j = 0 := by decide
      have he : levelSixEtaQuotient ![2, -4, -2, 4] = hauptmodulEta :=
        funext levelSixEtaQuotient_eq_hauptmodulEta
      simpa only [he] using
        isBoundedAtImInfty_modularLogDeriv_levelSixEtaQuotient_slash_rep _ hm i)

@[simp] theorem hauptmodulLogDerivativeForm_apply (τ : ℍ) :
    hauptmodulLogDerivativeForm τ = modularLogDeriv hauptmodulEta τ := rfl

theorem tendsto_modularLogDeriv_hauptmodulEta :
    Tendsto (fun τ : ℍ => modularLogDeriv hauptmodulEta τ) atImInfty (𝓝 1) := by
  have ht := tendsto_modularLogDeriv_dedekindEta_sq_affine_prod ![2, -4, -2, 4]
    (fun j => (levelSixEtaScale j : ℝ)) (fun _ => 0)
    (fun j => by
      change (0 : ℝ) < levelSixEtaScale j
      exact_mod_cast levelSixEtaScale_pos j)
  have he : (fun z : ℂ => ∏ j,
      (dedekindEta (((levelSixEtaScale j : ℝ) : ℂ) * z + ((0 : ℝ) : ℂ)) ^ 2) ^
        (![2, -4, -2, 4] : Fin 4 → ℤ) j) = hauptmodulEta := by
    ext z
    simpa only [ofReal_natCast, ofReal_zero, add_zero, levelSixEtaQuotient] using
      levelSixEtaQuotient_eq_hauptmodulEta z
  rw [he] at ht
  norm_num [Fin.sum_univ_four, levelSixEtaScale, Matrix.cons_val_two, Matrix.cons_val_three] at ht
  exact ht

end DirichletL

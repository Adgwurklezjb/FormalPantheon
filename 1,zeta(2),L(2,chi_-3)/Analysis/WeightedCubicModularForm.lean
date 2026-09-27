import Analysis.WeightedCubicConvergence
import Analysis.ModularSlash

/-!
The full weighted cubic sums are modular forms on the principal level-six group.
This supplies cusp bounds for the character series of CDT v2, Section 11.1,
-/

namespace DirichletL

open Matrix EisensteinSeries SlashInvariantForm CongruenceSubgroup
open _root_.UpperHalfPlane
open scoped Topology MatrixGroups ModularForm

theorem isBoundedAtImInfty_weightedCubicEisenstein (w : (Fin 2 → ZMod 6) → ℂ) :
    IsBoundedAtImInfty (weightedCubicEisenstein w) := by
  rw [isBoundedAtImInfty_iff]
  refine ⟨∑' v : Fin 2 → ℤ,
    ‖w‖ * (r ⟨⟨6, 2⟩, by norm_num⟩ ^ (-3 : ℤ) * ‖v‖ ^ (-3 : ℤ)), 2, ?_⟩
  intro τ hτ
  obtain ⟨n, hn⟩ := ModularGroup_T_zpow_mem_verticalStrip τ (by norm_num : 0 < (6 : ℕ))
  have ht := T_zpow_width_invariant 6 3 n (weightedCubicEisensteinSIF w) τ
  simp only [weightedCubicEisensteinSIF_apply] at ht
  rw [← ht, weightedCubicEisenstein]
  refine (norm_tsum_le_tsum_norm (summable_norm_weightedCubicEisenstein w _)).trans ?_
  have hs : Summable (fun v : Fin 2 → ℤ => ‖v‖ ^ (-3 : ℤ)) := by
    exact_mod_cast summable_one_div_norm_rpow (by norm_num : (2 : ℝ) < 3)
  apply (summable_norm_weightedCubicEisenstein w _).tsum_le_tsum
  · intro v
    exact norm_weightedCubicSummand_le w v (by norm_num) (verticalStrip_anti_right 6 hτ hn)
  · exact (hs.mul_left (r ⟨⟨6, 2⟩, by norm_num⟩ ^ (-3 : ℤ))).mul_left ‖w‖

theorem isBoundedAtImInfty_weightedCubicEisenstein_slash
    (w : (Fin 2 → ZMod 6) → ℂ) (A : SL(2, ℤ)) :
    IsBoundedAtImInfty (weightedCubicEisenstein w ∣[(3 : ℤ)] A) := by
  rw [weightedCubicEisenstein_slash]
  exact isBoundedAtImInfty_weightedCubicEisenstein _

/-- The full cubic Eisenstein sum with a residue weight, as a level-six modular form. -/
noncomputable def weightedCubicEisensteinForm (w : (Fin 2 → ZMod 6) → ℂ) :
    ModularForm (Gamma 6) 3 where
  toSlashInvariantForm := weightedCubicEisensteinSIF w
  holo' := weightedCubicEisenstein_MDifferentiable w
  bdd_at_cusps' := isBoundedAt_cusp_of_slash_SL2
    (isBoundedAtImInfty_weightedCubicEisenstein_slash w)

@[simp] theorem weightedCubicEisensteinForm_apply (w : (Fin 2 → ZMod 6) → ℂ) (τ : ℍ) :
    weightedCubicEisensteinForm w τ = weightedCubicEisenstein w τ := rfl

end DirichletL

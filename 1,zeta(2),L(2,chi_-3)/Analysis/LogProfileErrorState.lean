import Analysis.LogProfileState
import Analysis.LevelTwoLogRemainder

/-!
Initial whole-cell profile state for CDT v2, TeX 8384-8404.
Meanings and nonvanishing checks precede these bodies in
-/

namespace DirichletL

/-- Finite profile data together with powers of a norm bound and an accumulated error. -/
structure LogProfileErrorState where
  /-- Enclosed midpoint power, product, and combined slope. -/
  profile : LogProfileState
  /-- Enclosure of the current power of the common norm bound. -/
  rhoPower : NonemptyInterval ℤ
  /-- Enclosure of the previous power, or one at index zero. -/
  previousRhoPower : NonemptyInterval ℤ
  /-- Interval whose upper endpoint bounds the absolute nonlinear remainder. -/
  error : NonemptyInterval ℤ
  deriving DecidableEq

namespace LogProfileErrorState

/-- Every data field's meaning, with nonvanishing and a remainder bound on the whole nome disc. -/
structure Interprets (D : ℕ) (q₀ : ℂ) (ρ δ : ℚ) (n : ℕ)
    (S : LogProfileErrorState) : Prop where
  /-- The variation radius is nonnegative. -/
  delta_nonneg : 0 ≤ (δ : ℝ)
  /-- The reference nome satisfies the common norm bound. -/
  norm_le : ‖q₀‖ ≤ (ρ : ℝ)
  /-- The complete displacement disc excludes zero. -/
  nonzero : ∀ q : ℂ, ‖q - q₀‖ ≤ (δ : ℝ) → q ≠ 0
  /-- The simultaneous midpoint data are interpreted at the current index. -/
  profile : LogProfileState.Interprets D q₀ n S.profile
  /-- The current norm-bound power belongs to its interval. -/
  rho_power : (ρ : ℝ) ^ n ∈ ScaledInterval.denote D S.rhoPower
  /-- The preceding norm-bound power belongs to its interval. -/
  previous_rho_power : (ρ : ℝ) ^ (n - 1) ∈ ScaledInterval.denote D S.previousRhoPower
  /-- The nonlinear error is bounded for every nome satisfying the norm and displacement bounds. -/
  remainder : ∀ q : ℂ, ‖q‖ ≤ (ρ : ℝ) → ‖q - q₀‖ ≤ (δ : ℝ) →
    |levelTwoLogRemainder n q q₀| ≤ (S.error.snd : ℝ) / D

/-- Initialize the logarithmic error after checking a positive distance from zero. -/
def init? (D : ℕ) (δ : ℚ) (Q : ScaledRectangle) : Option LogProfileErrorState := do
  let β := ScaledRectangle.normLower D Q
  if 0 ≤ δ ∧ δ < β then
    let P ← LogProfileState.init? D Q
    return ⟨P, ScaledInterval.ofRat D 1, ScaledInterval.ofRat D 1,
      ScaledInterval.ofRat D (δ ^ 2 / (2 * β * (β - δ)))⟩
  else none

theorem init?_interprets {D : ℕ} (hD : 0 < D) (ρ δ : ℚ) {Q : ScaledRectangle}
    {q₀ : ℂ} {S : LogProfileErrorState} (hS : init? D δ Q = some S)
    (hq₀ : q₀ ∈ ScaledRectangle.denote D Q) (hρ : ‖q₀‖ ≤ (ρ : ℝ)) :
    Interprets D q₀ ρ δ 0 S := by
  dsimp only [init?] at hS
  split at hS
  · rename_i hguard
    rcases Option.bind_eq_some.mp hS with ⟨P, hP, hS⟩
    cases Option.some.inj hS
    have hδ0 : (0 : ℝ) ≤ δ := by exact_mod_cast hguard.1
    have hsmall : (δ : ℝ) < (ScaledRectangle.normLower D Q : ℝ) := by
      exact_mod_cast hguard.2
    have hβ := ScaledRectangle.normLower_le_norm hD hq₀
    have h1 : (1 : ℝ) ∈ ScaledInterval.denote D (ScaledInterval.ofRat D 1) := by
      simpa only [Rat.cast_one] using ScaledInterval.ofRat_mem hD 1
    refine ⟨hδ0, hρ, ?_, LogProfileState.init?_interprets hD hP hq₀,
      by simpa only [pow_zero] using h1, by simpa only [Nat.zero_sub, pow_zero] using h1, ?_⟩
    · intro q hδ hq
      have hbad : ‖q₀‖ ≤ (δ : ℝ) := by simpa only [hq, zero_sub, norm_neg] using hδ
      exact (not_le_of_gt hsmall) (hβ.trans hbad)
    · intro q _ hδ
      have hr : |levelTwoLogRemainder 0 q q₀| ≤
          (δ : ℝ) ^ 2 / (2 * (ScaledRectangle.normLower D Q : ℝ) *
            ((ScaledRectangle.normLower D Q : ℝ) - (δ : ℝ))) := by
        rw [levelTwoLogRemainder_zero]
        simpa only [div_eq_mul_inv, mul_comm] using
          abs_log_norm_sub_sub_re_le hβ hδ hsmall
      apply hr.trans
      have he := (ScaledInterval.ofRat_mem hD
        (δ ^ 2 / (2 * ScaledRectangle.normLower D Q *
          (ScaledRectangle.normLower D Q - δ)))).2
      push_cast at he
      exact he
  · cases hS

end LogProfileErrorState
end DirichletL

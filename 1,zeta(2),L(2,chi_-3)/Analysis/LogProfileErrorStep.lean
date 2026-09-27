import Analysis.LogProfileErrorState
import Analysis.LogProfilePowerBounds

/-!
Checked whole-cell error transitions for CDT v2's finite profile, TeX 8384-8404.
Meanings and all strict factor guards precede these bodies in
-/

namespace DirichletL.LogProfileErrorState

/-- Add one product factor, checking its complete displacement disc before updating the error. -/
def step? (D : ℕ) (ρ δ : ℚ) (Q : ScaledRectangle) (n : ℕ)
    (S : LogProfileErrorState) : Option LogProfileErrorState := do
  let P ← LogProfileState.step? D Q n S.profile
  let β := ScaledRectangle.normLower D (ScaledRectangle.ofRat D 1 + P.power)
  let ε := ScaledInterval.powerDifferenceRadius D δ n S.rhoPower
  let p := ScaledInterval.powerRemainderRadius D δ n S.previousRhoPower
  if ε < β then
    return ⟨P, ScaledInterval.mul D S.rhoPower (ScaledInterval.ofRat D ρ), S.rhoPower,
      S.error + ScaledInterval.mul D (ScaledInterval.ofRat D 24)
        (ScaledInterval.ofRat D (p / β) +
          ScaledInterval.ofRat D (ε ^ 2 / (2 * β * (β - ε))))⟩
  else none

theorem step?_interprets {D : ℕ} (hD : 0 < D) (ρ δ : ℚ)
    {Q : ScaledRectangle} {q₀ : ℂ} {n : ℕ} {S T : LogProfileErrorState}
    (hT : step? D ρ δ Q n S = some T) (hq₀ : q₀ ∈ ScaledRectangle.denote D Q)
    (hS : Interprets D q₀ ρ δ n S) : Interprets D q₀ ρ δ (n + 1) T := by
  dsimp only [step?] at hT
  rcases Option.bind_eq_some.mp hT with ⟨P, hP, hT⟩
  split at hT
  · rename_i hguard
    cases Option.some.inj hT
    have hp := LogProfileState.step?_interprets hD hP hq₀ hS.profile
    have h1 : (1 : ℂ) ∈ ScaledRectangle.denote D (ScaledRectangle.ofRat D 1) := by
      simpa only [Rat.cast_one] using ScaledRectangle.ofRat_mem hD 1
    have hβ := ScaledRectangle.normLower_le_norm hD (ScaledRectangle.add_mem hD h1 hp.1)
    have hε := ScaledInterval.le_powerDifferenceRadius hD δ n hS.rho_power
    have hquadratic := ScaledInterval.le_powerRemainderRadius hD δ n hS.previous_rho_power
    refine ⟨hS.delta_nonneg, hS.norm_le, hS.nonzero, hp, ?_, ?_, ?_⟩
    · simpa only [pow_succ] using
        ScaledInterval.mul_mem hD hS.rho_power (ScaledInterval.ofRat_mem hD ρ)
    · simpa only [Nat.add_sub_cancel] using hS.rho_power
    · intro q hq hδ
      have hf := abs_log_pow_factor_remainder_le n hq hS.norm_le hδ hβ hε hquadratic
        (by exact_mod_cast hguard)
      have hupper : (S.error.snd : ℝ) / D ∈ ScaledInterval.denote D S.error := by
        exact ⟨div_le_div_of_nonneg_right (by exact_mod_cast S.error.fst_le_snd)
          (Nat.cast_nonneg D), le_rfl⟩
      have he := ScaledInterval.add_mem hD hupper
        (ScaledInterval.mul_mem hD (ScaledInterval.ofRat_mem hD 24)
          (ScaledInterval.add_mem hD
            (ScaledInterval.ofRat_mem hD
              (ScaledInterval.powerRemainderRadius D δ n S.previousRhoPower /
                ScaledRectangle.normLower D (ScaledRectangle.ofRat D 1 + P.power)))
            (ScaledInterval.ofRat_mem hD
              ((ScaledInterval.powerDifferenceRadius D δ n S.rhoPower) ^ 2 /
                (2 * ScaledRectangle.normLower D (ScaledRectangle.ofRat D 1 + P.power) *
                  (ScaledRectangle.normLower D (ScaledRectangle.ofRat D 1 + P.power) -
                    ScaledInterval.powerDifferenceRadius D δ n S.rhoPower))))))
      rw [levelTwoLogRemainder_succ]
      have hf24 := mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 24)
      rw [← abs_of_pos (by norm_num : (0 : ℝ) < 24), ← abs_mul] at hf24
      simp only [abs_of_pos (by norm_num : (0 : ℝ) < 24)] at hf24
      apply ((abs_add_le _ _).trans (add_le_add (hS.remainder q hq hδ) hf24)).trans
      simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_div,
        Rat.cast_pow, Rat.cast_sub] using he.2
  · cases hT

/-- Accumulate the checked whole-cell error through exactly `n` factors. -/
def iterate? (D : ℕ) (ρ δ : ℚ) (Q : ScaledRectangle) : ℕ → Option LogProfileErrorState
  | 0 => init? D δ Q
  | n + 1 => do
    let S ← iterate? D ρ δ Q n
    step? D ρ δ Q n S

theorem iterate?_interprets {D : ℕ} (hD : 0 < D) (ρ δ : ℚ)
    {Q : ScaledRectangle} {q₀ : ℂ} (hq₀ : q₀ ∈ ScaledRectangle.denote D Q)
    (hρ : ‖q₀‖ ≤ (ρ : ℝ)) (n : ℕ) {S : LogProfileErrorState}
    (hS : iterate? D ρ δ Q n = some S) : Interprets D q₀ ρ δ n S := by
  induction n generalizing S with
  | zero => exact init?_interprets hD ρ δ hS hq₀ hρ
  | succ n ih =>
    rcases Option.bind_eq_some.mp hS with ⟨T, hT, hS⟩
    exact step?_interprets hD ρ δ hS hq₀ (ih hT)

end DirichletL.LogProfileErrorState

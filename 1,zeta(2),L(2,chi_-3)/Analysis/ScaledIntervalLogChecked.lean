import Analysis.ScaledIntervalLog
import Analysis.ScaledRationalBounds

/-!
Checked endpoint logarithms for CDT v2's product profile, TeX 6947-6948 and 8384-8404.
Meanings and normalization guards precede these bodies in
-/

namespace DirichletL.ScaledInterval

/-- Normalize a positive rational by a supplied integer power of two, checking both endpoints. -/
def logRat? (D : ℕ) (k : ℤ) (q : ℚ) : Option (NonemptyInterval ℤ) :=
  let Y := ofRat D (q / (2 : ℚ) ^ k)
  if 0 < q ∧ (D : ℤ) ≤ Y.fst ∧ Y.snd ≤ 2 * (D : ℤ) then
    some (logScaled D k Y)
  else none

theorem logRat?_mem {D : ℕ} (hD : 0 < D) (k : ℤ) (q : ℚ)
    {J : NonemptyInterval ℤ} (hJ : logRat? D k q = some J) :
    Real.log (q : ℝ) ∈ denote D J := by
  dsimp only [logRat?] at hJ
  split at hJ
  · rename_i hguard
    cases Option.some.inj hJ
    have h := logScaled_mem hD k hguard.2.1 hguard.2.2
      (ofRat_mem hD (q / (2 : ℚ) ^ k))
    have heq : (2 : ℝ) ^ k * ((q / (2 : ℚ) ^ k : ℚ) : ℝ) = q := by
      push_cast
      field_simp
    simpa only [heq] using h
  · cases hJ

/-- Enclose a positive interval's logarithm by checked lower and upper endpoint evaluations. -/
def log? (D : ℕ) (k : ℤ × ℤ) (I : NonemptyInterval ℤ) :
    Option (NonemptyInterval ℤ) := do
  if 0 < I.fst then
    let L ← logRat? D k.1 ((I.fst : ℚ) / D)
    let U ← logRat? D k.2 ((I.snd : ℚ) / D)
    return NonemptyInterval.pure L.fst ⊔ NonemptyInterval.pure U.snd
  else none

theorem log?_mem {D : ℕ} (hD : 0 < D) (k : ℤ × ℤ)
    {I J : NonemptyInterval ℤ} {x : ℝ}
    (hJ : log? D k I = some J) (hx : x ∈ denote D I) :
    Real.log x ∈ denote D J := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  dsimp only [log?] at hJ
  split at hJ
  · rename_i hpos
    rcases Option.bind_eq_some.mp hJ with ⟨L, hL, hJ⟩
    rcases Option.bind_eq_some.mp hJ with ⟨U, hU, hJ⟩
    cases Option.some.inj hJ
    have hl := logRat?_mem hD k.1 _ hL
    have hu := logRat?_mem hD k.2 _ hU
    simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] at hl hu
    have hp : 0 < (I.fst : ℝ) / D := div_pos (by exact_mod_cast hpos) hDr
    apply mem_denote_hull hD
    · simpa only [mul_comm] using
        (div_le_iff₀ hDr).mp (hl.1.trans (Real.log_le_log hp hx.1))
    · simpa only [mul_comm] using
        (le_div_iff₀ hDr).mp ((Real.log_le_log (hp.trans_le hx.1) hx.2).trans hu.2)
  · cases hJ

end DirichletL.ScaledInterval

import Analysis.ContourInputEnclosures
import Analysis.ScaledIntervalLogChecked
import Analysis.ScaledRectangleChecked

/-!
Checked transformed nomes for CDT author Lemma A.4.4, page 205.
Meanings, translation signs, and guards precede the bodies in
-/

namespace DirichletL

private theorem qParam_one_eq_exp_sub_int (z : ℂ) (m : ℤ) :
    Function.Periodic.qParam 1 z =
      Complex.exp (2 * Real.pi * Complex.I * (z - (m : ℂ))) := by
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨m, ?_⟩
  ring

namespace ScaledRectangle

/-- Enclose the height of the positive real root's canonical period-one lift. -/
def levelTwoHeight? (D : ℕ) (Q : NonemptyInterval ℤ) :
    Option (NonemptyInterval ℤ) := do
  let L ← ScaledInterval.log? D (-15, -15) Q
  let P := ScaledInterval.mul D (ScaledInterval.ofRat D 2) (piInterval D)
  if 0 < P.fst then
    return ScaledInterval.mul D (-L) (ScaledInterval.inv D P)
  else none

theorem levelTwoHeight?_mem {D : ℕ} (hD : 0 < D)
    {Q T : NonemptyInterval ℤ} {q : ℝ}
    (hT : levelTwoHeight? D Q = some T)
    (hq0 : 0 < q) (hq : q ∈ ScaledInterval.denote D Q) :
    Function.Periodic.invQParam 1 (q : ℂ) ∈ denote D (0, T) := by
  dsimp only [levelTwoHeight?] at hT
  rcases Option.bind_eq_some.mp hT with ⟨L, hL, hT⟩
  split at hT
  · rename_i hP
    cases Option.some.inj hT
    have hpi : 2 * Real.pi ∈ ScaledInterval.denote D
        (ScaledInterval.mul D (ScaledInterval.ofRat D 2) (piInterval D)) := by
      simpa only [Rat.cast_ofNat] using
        ScaledInterval.mul_mem hD (ScaledInterval.ofRat_mem hD 2) (pi_mem hD)
    have ht := ScaledInterval.mul_mem hD
      (ScaledInterval.neg_mem hD (ScaledInterval.log?_mem hD (-15, -15) hL hq))
      (ScaledInterval.inv_mem hD hP hpi)
    constructor
    · have hre : (Function.Periodic.invQParam 1 (q : ℂ)).re = 0 := by
        simp [Function.Periodic.invQParam, ← Complex.ofReal_log hq0.le,
          Complex.mul_re, Complex.div_re]
      rw [hre]
      simp [ScaledInterval.denote]
    · rw [Function.Periodic.im_invQParam, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hq0]
      convert ht using 1
      ring
  · cases hT

/-- Evaluate a transformed nome after an exact integer translation in its exponent. -/
def levelTwoNome? (D : ℕ) (n m : ℤ) (T : NonemptyInterval ℤ) :
    Option ScaledRectangle := do
  let Z : ScaledRectangle := (0, T)
  let U ← div? D (Z + ofRat D (n : ℚ))
    (mul D (ofRat D 2) Z + ofRat D (2 * (n : ℚ) + 1))
  let P := ScaledInterval.mul D (ScaledInterval.ofRat D 2) (piInterval D)
  let E := mul D (0, P) (U - ofRat D (m : ℚ))
  if (normSq D E).snd ≤ 16 * (D : ℤ) then return exp48 D E else none

theorem levelTwoNome?_mem {D : ℕ} (hD : 0 < D) (n m : ℤ)
    {T : NonemptyInterval ℤ} {W : ScaledRectangle} {τ : ℂ}
    (hW : levelTwoNome? D n m T = some W) (hτ : τ ∈ denote D (0, T)) :
    Function.Periodic.qParam 1 ((τ + (n : ℂ)) /
      (2 * τ + (2 * (n : ℂ) + 1))) ∈ denote D W := by
  dsimp only [levelTwoNome?] at hW
  rcases Option.bind_eq_some.mp hW with ⟨U, hU, hW⟩
  split at hW
  · rename_i hguard
    cases Option.some.inj hW
    have hn : (n : ℂ) ∈ denote D (ofRat D (n : ℚ)) := by
      simpa only [Rat.cast_intCast] using ofRat_mem hD (n : ℚ)
    have hm : (m : ℂ) ∈ denote D (ofRat D (m : ℚ)) := by
      simpa only [Rat.cast_intCast] using ofRat_mem hD (m : ℚ)
    have htwo : (2 : ℂ) ∈ denote D (ofRat D 2) := by
      simpa only [Rat.cast_ofNat] using ofRat_mem hD 2
    have hd : 2 * (n : ℂ) + 1 ∈ denote D (ofRat D (2 * (n : ℚ) + 1)) := by
      simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_intCast,
        Rat.cast_one] using ofRat_mem hD (2 * (n : ℚ) + 1)
    have hu := div?_mem hD hU (add_mem hD hτ hn)
      (add_mem hD (mul_mem hD htwo hτ) hd)
    have hpi : 2 * Real.pi ∈ ScaledInterval.denote D
        (ScaledInterval.mul D (ScaledInterval.ofRat D 2) (piInterval D)) := by
      simpa only [Rat.cast_ofNat] using
        ScaledInterval.mul_mem hD (ScaledInterval.ofRat_mem hD 2) (pi_mem hD)
    have hpiI : 2 * (Real.pi : ℂ) * Complex.I ∈ denote D
        (0, ScaledInterval.mul D (ScaledInterval.ofRat D 2) (piInterval D)) := by
      constructor
      · simp [ScaledInterval.denote]
      · simpa only [Complex.mul_im, Complex.mul_re, Complex.re_ofNat,
          Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im, Complex.I_re,
          Complex.I_im, mul_zero, sub_zero, add_zero, zero_mul, mul_one] using hpi
    have he := mul_mem hD hpiI (sub_mem hD hu hm)
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    have hs := (normSq_mem hD he).2
    have he4 : ‖2 * (Real.pi : ℂ) * Complex.I *
        ((τ + (n : ℂ)) / (2 * τ + (2 * (n : ℂ) + 1)) - (m : ℂ))‖ ≤ 4 := by
      rw [Complex.normSq_eq_norm_sq] at hs
      have hb : _ ≤ (16 : ℝ) :=
        hs.trans ((div_le_iff₀ hDr).mpr (by exact_mod_cast hguard))
      nlinarith
    rw [qParam_one_eq_exp_sub_int _ m]
    exact exp48_mem hD he he4
  · cases hW

end ScaledRectangle
end DirichletL

import Analysis.LevelTwoLogRecurrences
import Analysis.ScaledIntervalLogChecked
import Analysis.ScaledRectangleChecked

/-!
Simultaneous midpoint product and slope for CDT v2, TeX 6947-6948 and 8384-8404.
All meanings and indexing checks precede these bodies in
-/

namespace DirichletL

/-- Rectangle enclosures of a nome power, a finite product, and its combined logarithmic slope. -/
structure LogProfileState where
  /-- The current power of the exact nome. -/
  power : ScaledRectangle
  /-- The product of all factors processed so far. -/
  product : ScaledRectangle
  /-- The combined complex linear coefficient, before taking its norm. -/
  slope : ScaledRectangle
  deriving DecidableEq

namespace LogProfileState

/-- The three data fields enclose the exact power, product, and finite-profile slope. -/
def Interprets (D : ℕ) (q : ℂ) (n : ℕ) (S : LogProfileState) : Prop :=
  q ^ n ∈ ScaledRectangle.denote D S.power ∧
    qPochhammer (-q) q n ∈ ScaledRectangle.denote D S.product ∧
    levelTwoLogSlope n q ∈ ScaledRectangle.denote D S.slope

/-- Start with the empty product and a checked reciprocal of the nome. -/
def init? (D : ℕ) (Q : ScaledRectangle) : Option LogProfileState := do
  let one := ScaledRectangle.ofRat D 1
  let V ← ScaledRectangle.div? D one Q
  return ⟨one, one, V⟩

theorem init?_interprets {D : ℕ} (hD : 0 < D) {Q : ScaledRectangle}
    {q : ℂ} {S : LogProfileState}
    (hS : init? D Q = some S) (hq : q ∈ ScaledRectangle.denote D Q) :
    Interprets D q 0 S := by
  dsimp only [init?] at hS
  rcases Option.bind_eq_some.mp hS with ⟨V, hV, hS⟩
  cases Option.some.inj hS
  have h1 : (1 : ℂ) ∈ ScaledRectangle.denote D (ScaledRectangle.ofRat D 1) := by
    simpa only [Rat.cast_one] using ScaledRectangle.ofRat_mem hD 1
  refine ⟨by simpa only [pow_zero] using h1, ?_, ?_⟩
  · simpa only [qPochhammer_zero] using h1
  · simpa [levelTwoLogSlope] using ScaledRectangle.div?_mem hD hV h1 hq

/-- Add the next factor and its complex linear coefficient using checked division. -/
def step? (D : ℕ) (Q : ScaledRectangle) (n : ℕ) (S : LogProfileState) :
    Option LogProfileState := do
  let P := ScaledRectangle.mul D S.power Q
  let F := ScaledRectangle.ofRat D 1 + P
  let V ← ScaledRectangle.div? D
    (ScaledRectangle.realMul D (ScaledInterval.ofRat D (24 * ((n + 1 : ℕ) : ℚ))) S.power) F
  return ⟨P, ScaledRectangle.mul D S.product F, S.slope + V⟩

theorem step?_interprets {D : ℕ} (hD : 0 < D) {Q : ScaledRectangle}
    {q : ℂ} {n : ℕ} {S T : LogProfileState}
    (hT : step? D Q n S = some T) (hq : q ∈ ScaledRectangle.denote D Q)
    (hS : Interprets D q n S) : Interprets D q (n + 1) T := by
  dsimp only [step?] at hT
  rcases Option.bind_eq_some.mp hT with ⟨V, hV, hT⟩
  cases Option.some.inj hT
  have h1 : (1 : ℂ) ∈ ScaledRectangle.denote D (ScaledRectangle.ofRat D 1) := by
    simpa only [Rat.cast_one] using ScaledRectangle.ofRat_mem hD 1
  have hp : q ^ (n + 1) ∈ ScaledRectangle.denote D (ScaledRectangle.mul D S.power Q) := by
    simpa only [pow_succ] using ScaledRectangle.mul_mem hD hS.1 hq
  have hf := ScaledRectangle.add_mem hD h1 hp
  have hc : 24 * ((n + 1 : ℕ) : ℂ) * q ^ n ∈ ScaledRectangle.denote D
      (ScaledRectangle.realMul D (ScaledInterval.ofRat D (24 * ((n + 1 : ℕ) : ℚ)))
        S.power) := by
    simpa only [Complex.ofReal_ratCast, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast] using
      ScaledRectangle.realMul_mem hD (ScaledInterval.ofRat_mem hD (24 * ((n + 1 : ℕ) : ℚ))) hS.1
  refine ⟨hp, ?_, ?_⟩
  · simpa only [qPochhammer_succ, neg_mul, sub_neg_eq_add, ← pow_succ'] using
      ScaledRectangle.mul_mem hD hS.2.1 hf
  · rw [levelTwoLogSlope_succ]
    exact ScaledRectangle.add_mem hD hS.2.2 (ScaledRectangle.div?_mem hD hV hc hf)

/-- Evaluate exactly the first `n` product factors and their combined slope. -/
def iterate? (D : ℕ) (Q : ScaledRectangle) : ℕ → Option LogProfileState
  | 0 => init? D Q
  | n + 1 => do
    let S ← iterate? D Q n
    step? D Q n S

theorem iterate?_interprets {D : ℕ} (hD : 0 < D) {Q : ScaledRectangle}
    {q : ℂ} (hq : q ∈ ScaledRectangle.denote D Q) (n : ℕ)
    {S : LogProfileState} (hS : iterate? D Q n = some S) :
    Interprets D q n S := by
  induction n generalizing S with
  | zero => exact init?_interprets hD hS hq
  | succ n ih =>
    rcases Option.bind_eq_some.mp hS with ⟨T, hT, hS⟩
    exact step?_interprets hD hS hq (ih hT)

/-- Evaluate the finite logarithmic profile from the enclosed nome and product. -/
def logPartial? (D : ℕ) (Q : ScaledRectangle) (S : LogProfileState)
    (kq kp : ℤ × ℤ) : Option (NonemptyInterval ℤ) := do
  let A ← ScaledInterval.log? D kq (ScaledRectangle.normSq D Q)
  let B ← ScaledInterval.log? D kp (ScaledRectangle.normSq D S.product)
  return ScaledInterval.mul D (ScaledInterval.ofRat D 8) (ScaledInterval.logTwo D) +
    ScaledInterval.mul D (ScaledInterval.ofRat D (1 / 2)) A +
    ScaledInterval.mul D (ScaledInterval.ofRat D 12) B

theorem logPartial?_mem {D : ℕ} (hD : 0 < D) {Q : ScaledRectangle}
    {q : ℂ} {n : ℕ} {S : LogProfileState} (kq kp : ℤ × ℤ)
    {I : NonemptyInterval ℤ} (hI : logPartial? D Q S kq kp = some I)
    (hq : q ∈ ScaledRectangle.denote D Q) (hS : Interprets D q n S)
    (hq1 : ‖q‖ < 1) : levelTwoLogPartial n q ∈ ScaledInterval.denote D I := by
  rcases Option.bind_eq_some.mp hI with ⟨A, hA, hI⟩
  rcases Option.bind_eq_some.mp hI with ⟨B, hB, hI⟩
  cases Option.some.inj hI
  have ha := ScaledInterval.log?_mem hD kq hA (ScaledRectangle.normSq_mem hD hq)
  have hb := ScaledInterval.log?_mem hD kp hB (ScaledRectangle.normSq_mem hD hS.2.1)
  rw [levelTwoLogPartial_eq_log_normSq_qPochhammer n hq1]
  simpa only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_one] using
    ScaledInterval.add_mem hD
      (ScaledInterval.add_mem hD
        (ScaledInterval.mul_mem hD (ScaledInterval.ofRat_mem hD 8) (ScaledInterval.logTwo_mem hD))
        (ScaledInterval.mul_mem hD (ScaledInterval.ofRat_mem hD (1 / 2)) ha))
      (ScaledInterval.mul_mem hD (ScaledInterval.ofRat_mem hD 12) hb)

end LogProfileState
end DirichletL

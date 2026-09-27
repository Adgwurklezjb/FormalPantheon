import Analysis.ScaledRootCertificate
import Analysis.LogProfileErrorStep

/-!
Checked root data for CDT's finite-profile error, supplied TeX 8384-8404.
-/

namespace DirichletL.LogProfileErrorState

/-- Initialize with a checked norm while retaining every canonical initial guard. -/
def initWithRoots? (D : ℕ) (δ : ℚ) (Q : ScaledRectangle) (roots : ℕ × ℕ) :
    Option LogProfileErrorState := do
  let I ← ScaledRectangle.norm? D Q roots
  let β := (I.fst : ℚ) / D
  if 0 ≤ δ ∧ δ < β then
    let P ← LogProfileState.init? D Q
    return ⟨P, ScaledInterval.ofRat D 1, ScaledInterval.ofRat D 1,
      ScaledInterval.ofRat D (δ ^ 2 / (2 * β * (β - δ)))⟩
  else none

theorem initWithRoots?_eq {D : ℕ} {δ : ℚ} {Q : ScaledRectangle}
    {roots : ℕ × ℕ} {S : LogProfileErrorState}
    (h : initWithRoots? D δ Q roots = some S) : init? D δ Q = some S := by
  dsimp only [initWithRoots?] at h
  rcases Option.bind_eq_some.mp h with ⟨I, hI, h⟩
  rw [ScaledRectangle.norm?_eq hI] at h
  exact h

/-- Check the actual next factor's norm before the unchanged canonical error update. -/
def stepWithRoots? (D : ℕ) (ρ δ : ℚ) (Q : ScaledRectangle) (n : ℕ)
    (S : LogProfileErrorState) (roots : ℕ × ℕ) : Option LogProfileErrorState := do
  let P ← LogProfileState.step? D Q n S.profile
  let I ← ScaledRectangle.norm? D (ScaledRectangle.ofRat D 1 + P.power) roots
  let β := (I.fst : ℚ) / D
  let ε := ScaledInterval.powerDifferenceRadius D δ n S.rhoPower
  let p := ScaledInterval.powerRemainderRadius D δ n S.previousRhoPower
  if ε < β then
    return ⟨P, ScaledInterval.mul D S.rhoPower (ScaledInterval.ofRat D ρ), S.rhoPower,
      S.error + ScaledInterval.mul D (ScaledInterval.ofRat D 24)
        (ScaledInterval.ofRat D (p / β) +
          ScaledInterval.ofRat D (ε ^ 2 / (2 * β * (β - ε))))⟩
  else none

theorem stepWithRoots?_eq {D : ℕ} {ρ δ : ℚ} {Q : ScaledRectangle} {n : ℕ}
    {S T : LogProfileErrorState} {roots : ℕ × ℕ}
    (h : stepWithRoots? D ρ δ Q n S roots = some T) : step? D ρ δ Q n S = some T := by
  dsimp only [stepWithRoots?] at h
  rcases Option.bind_eq_some.mp h with ⟨P, hP, h⟩
  rcases Option.bind_eq_some.mp h with ⟨I, hI, h⟩
  rw [ScaledRectangle.norm?_eq hI] at h
  exact Option.bind_eq_some.mpr ⟨P, hP, h⟩

/-- Consume each root pair in order, advancing the factor index once per pair. -/
def iterateWithRoots? (D : ℕ) (ρ δ : ℚ) (Q : ScaledRectangle) (n : ℕ)
    (S : LogProfileErrorState) : List (ℕ × ℕ) → Option LogProfileErrorState
  | [] => some S
  | roots :: tail => do
    let T ← stepWithRoots? D ρ δ Q n S roots
    iterateWithRoots? D ρ δ Q (n + 1) T tail

theorem iterateWithRoots?_eq {D : ℕ} {ρ δ : ℚ} {Q : ScaledRectangle} {n : ℕ}
    {S T : LogProfileErrorState} {roots : List (ℕ × ℕ)}
    (hS : iterate? D ρ δ Q n = some S)
    (hT : iterateWithRoots? D ρ δ Q n S roots = some T) :
    iterate? D ρ δ Q (n + roots.length) = some T := by
  induction roots generalizing n S with
  | nil =>
    cases Option.some.inj hT
    simpa only [List.length_nil, Nat.add_zero] using hS
  | cons roots tail ih =>
    rcases Option.bind_eq_some.mp hT with ⟨U, hU, hT⟩
    have hnext : iterate? D ρ δ Q (n + 1) = some U :=
      Option.bind_eq_some.mpr ⟨S, hS, stepWithRoots?_eq hU⟩
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using ih hnext hT

end DirichletL.LogProfileErrorState

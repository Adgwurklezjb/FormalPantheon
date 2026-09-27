import Analysis.LogProfileErrorCertificate
import Analysis.CenteredLogProfile

/-!
Compact checked root data for CDT's complete profile, supplied TeX 6947-6948 and 8384-8404.
-/

namespace DirichletL.CenteredRectangle

/-- Check root data for exactly 100 factors and retain the complete profile's original output. -/
def logProfileWithRoots? (D : ℕ) (B : CenteredRectangle)
    (nomeRoots slopeRoots : ℕ × ℕ) (factorRoots : List (ℕ × ℕ)) (kq kp : ℤ × ℤ) :
    Option (NonemptyInterval ℤ) :=
  if factorRoots.length = 100 then do
    let R ← ScaledRectangle.norm? D B.center nomeRoots
    let ρ := min (77 / 100) (ScaledInterval.roundUp D ((R.snd : ℚ) / D + B.radius))
    let S ← LogProfileErrorState.initWithRoots? D B.radius B.center nomeRoots
    let T ← LogProfileErrorState.iterateWithRoots? D ρ B.radius B.center 0 S factorRoots
    let U ← ScaledRectangle.norm? D T.profile.slope slopeRoots
    let I ← LogProfileState.logPartial? D B.center T.profile kq kp
    let E := ScaledInterval.ofRat D (((U.snd : ℚ) / D) * B.radius) +
      T.error + ScaledInterval.ofRat D (1 / 100000000)
    return ScaledInterval.inflate E.snd I
  else none

theorem logProfileWithRoots?_eq {D : ℕ} {B : CenteredRectangle}
    {nomeRoots slopeRoots : ℕ × ℕ} {factorRoots : List (ℕ × ℕ)} {kq kp : ℤ × ℤ}
    {I : NonemptyInterval ℤ}
    (h : logProfileWithRoots? D B nomeRoots slopeRoots factorRoots kq kp = some I) :
    logProfile? D B kq kp = some I := by
  dsimp only [logProfileWithRoots?] at h
  split at h
  · rename_i hcount
    rcases Option.bind_eq_some.mp h with ⟨R, hR, h⟩
    rcases Option.bind_eq_some.mp h with ⟨S, hS, h⟩
    rcases Option.bind_eq_some.mp h with ⟨T, hT, h⟩
    rcases Option.bind_eq_some.mp h with ⟨U, hU, h⟩
    rcases Option.bind_eq_some.mp h with ⟨J, hJ, h⟩
    have hρ : min (77 / 100) (ScaledInterval.roundUp D ((R.snd : ℚ) / D + B.radius)) =
        profileNormBound D B := by
      rw [ScaledRectangle.norm?_eq hR]
      rfl
    rw [hρ] at hT
    have hinit : LogProfileErrorState.iterate? D (profileNormBound D B)
        B.radius B.center 0 = some S := LogProfileErrorState.initWithRoots?_eq hS
    have hiter : LogProfileErrorState.iterate? D (profileNormBound D B)
        B.radius B.center 100 = some T := by
      simpa only [Nat.zero_add, hcount] using
        LogProfileErrorState.iterateWithRoots?_eq hinit hT
    rw [ScaledRectangle.norm?_eq hU] at h
    dsimp only [logProfile?]
    apply Option.bind_eq_some.mpr
    refine ⟨T, hiter, ?_⟩
    apply Option.bind_eq_some.mpr
    exact ⟨J, hJ, h⟩
  · cases h

theorem logProfileWithRoots?_mem {D : ℕ} (hD : 0 < D)
    {B : CenteredRectangle} {q q₀ : ℂ} (kq kp : ℤ × ℤ)
    {nomeRoots slopeRoots : ℕ × ℕ} {factorRoots : List (ℕ × ℕ)}
    {I : NonemptyInterval ℤ}
    (hI : logProfileWithRoots? D B nomeRoots slopeRoots factorRoots kq kp = some I)
    (h : Encloses D B q q₀) (hq : ‖q‖ ≤ 77 / 100) (hq₀ : ‖q₀‖ ≤ 77 / 100) :
    Real.log ‖levelTwoHauptmodul q‖ ∈ ScaledInterval.denote D I :=
  logProfile?_mem hD kq kp (logProfileWithRoots?_eq hI) h hq hq₀

end DirichletL.CenteredRectangle

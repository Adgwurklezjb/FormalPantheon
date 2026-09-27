import Analysis.CenteredRectangleCertificate
import Analysis.CenteredContourComponents

/-!
Checked root data for CDT's slit and lune compositions, author Appendix A.4 page 204.
Complete meanings and guards precede these bodies in
-/

namespace DirichletL.CenteredRectangle

/-- Root data for the successive Cayley, quadratic, and principal-root operations. -/
structure HalfPlaneRootCertificate where
  /-- Denominator norm roots for the forward Cayley map. -/
  cayleyRoots : ℕ × ℕ
  /-- Midpoint norm roots for the quadratic argument's radius. -/
  argumentRoots : ℕ × ℕ
  /-- Principal-root data for the resulting quadratic cell. -/
  root : RootCertificate

/-- Check each stage of the canonical half-plane root composition. -/
def rootAfterCayleyWithRoots? (D : ℕ) (d : ℚ) (B : CenteredRectangle)
    (cert : HalfPlaneRootCertificate) : Option CenteredRectangle := do
  let C ← cayleyWithRoots? D B cert.cayleyRoots
  let A ← affineSquareWithRoots? D d C cert.argumentRoots
  sqrtWithRoots? D A cert.root

theorem rootAfterCayleyWithRoots?_eq {D : ℕ} {d : ℚ} {B C : CenteredRectangle}
    {cert : HalfPlaneRootCertificate}
    (h : rootAfterCayleyWithRoots? D d B cert = some C) :
    rootAfterCayley? D d B = some C := by
  dsimp only [rootAfterCayleyWithRoots?] at h
  rcases Option.bind_eq_some.mp h with ⟨V, hV, h⟩
  rcases Option.bind_eq_some.mp h with ⟨A, hA, h⟩
  have hs := sqrtWithRoots?_eq h
  rw [affineSquareWithRoots?_eq hA] at hs
  exact Option.bind_eq_some.mpr ⟨V, cayleyWithRoots?_eq hV, hs⟩

/-- Root data for the half-plane root and final inverse Cayley operation of a slit. -/
structure SlitCertificate where
  /-- Complete half-plane root certificate at the canonical slit coefficient. -/
  root : HalfPlaneRootCertificate
  /-- Denominator norm roots for the inverse Cayley map. -/
  inverseRoots : ℕ × ℕ

/-- Evaluate the canonical slit with checked root data at both stages. -/
def slitWithRoots? (D : ℕ) (r : ℚ) (B : CenteredRectangle)
    (cert : SlitCertificate) : Option CenteredRectangle := do
  let K ← rootAfterCayleyWithRoots? D (4 * r / (1 + r) ^ 2) B cert.root
  inverseCayleyWithRoots? D K cert.inverseRoots

theorem slitWithRoots?_eq {D : ℕ} {r : ℚ} {B C : CenteredRectangle}
    {cert : SlitCertificate} (h : slitWithRoots? D r B cert = some C) :
    slit? D r B = some C := by
  rcases Option.bind_eq_some.mp h with ⟨K, hK, h⟩
  exact Option.bind_eq_some.mpr
    ⟨K, rootAfterCayleyWithRoots?_eq hK, inverseCayleyWithRoots?_eq h⟩

/-- Root data for the half-plane root and two variation norms of a lune. -/
structure LuneCertificate where
  /-- Complete half-plane root certificate at the squared lune coefficient. -/
  root : HalfPlaneRootCertificate
  /-- Norm roots for one minus the input midpoint. -/
  inputRoots : ℕ × ℕ
  /-- Norm roots for the computed root midpoint minus one. -/
  outputRoots : ℕ × ℕ

/-- Evaluate the canonical lune with its coefficient, division, and root guards. -/
def luneWithRoots? (D : ℕ) (c : ℚ) (B : CenteredRectangle)
    (cert : LuneCertificate) : Option CenteredRectangle := do
  if 1 < c then
    let a := (c ^ 2 - 1) / (c ^ 2 + 1)
    let K ← rootAfterCayleyWithRoots? D (a ^ 2) B cert.root
    let one := ScaledRectangle.ofRat D 1
    let V ← ScaledRectangle.div? D (one - B.center) (ScaledRectangle.ofRat D (2 * a))
    let U ← ScaledRectangle.norm? D (one - B.center) cert.inputRoots
    let T ← ScaledRectangle.norm? D (K.center - one) cert.outputRoots
    return ⟨ScaledRectangle.mul D V (K.center - one),
      ScaledInterval.roundUp D
        (((((U.snd : ℚ) / D) + B.radius) * K.radius + B.radius * ((T.snd : ℚ) / D)) /
          (2 * a))⟩
  else none

theorem luneWithRoots?_eq {D : ℕ} {c : ℚ} {B C : CenteredRectangle}
    {cert : LuneCertificate} (h : luneWithRoots? D c B cert = some C) :
    lune? D c B = some C := by
  dsimp only [luneWithRoots?] at h
  unfold lune?
  by_cases hc : 1 < c
  · rw [if_pos hc] at h ⊢
    rcases Option.bind_eq_some.mp h with ⟨K, hK, h⟩
    rcases Option.bind_eq_some.mp h with ⟨V, hV, h⟩
    rcases Option.bind_eq_some.mp h with ⟨U, hU, h⟩
    rcases Option.bind_eq_some.mp h with ⟨T, hT, h⟩
    rw [ScaledRectangle.norm?_eq hU, ScaledRectangle.norm?_eq hT] at h
    exact Option.bind_eq_some.mpr ⟨K, rootAfterCayleyWithRoots?_eq hK,
      Option.bind_eq_some.mpr ⟨V, hV, h⟩⟩
  · rw [if_neg hc] at h
    cases h

end DirichletL.CenteredRectangle

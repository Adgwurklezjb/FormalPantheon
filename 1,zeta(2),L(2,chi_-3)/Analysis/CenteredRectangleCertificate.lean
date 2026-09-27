import Analysis.ScaledRectangleRootCertificate
import Analysis.CenteredRectangleCayley
import Analysis.CenteredRectangleRoot

/-!
Checked root data for CDT's centered contour operations, author Appendix A.4 page 204.
Complete meanings and pole checks precede these bodies in
-/

namespace DirichletL.CenteredRectangle

/-- Root proposals for the midpoint, whole-cell rectangle, and sum denominator. -/
structure RootCertificate where
  /-- Principal-root data for the midpoint rectangle. -/
  center : ScaledRectangle.RootCertificate
  /-- Principal-root data for the inflated whole-cell rectangle. -/
  wide : ScaledRectangle.RootCertificate
  /-- Norm roots of the actual sum of the two computed roots. -/
  sumRoots : ℕ × ℕ

/-- Evaluate the forward Cayley map with checked denominator norm roots. -/
def cayleyWithRoots? (D : ℕ) (B : CenteredRectangle) (roots : ℕ × ℕ) :
    Option CenteredRectangle := do
  let one := ScaledRectangle.ofRat D 1
  let N ← ScaledRectangle.norm? D (one - B.center) roots
  let β := (N.fst : ℚ) / D
  if B.radius < β then
    let W ← ScaledRectangle.div? D (one + B.center) (one - B.center)
    return ⟨W, ScaledInterval.roundUp D (2 * B.radius / (β * (β - B.radius)))⟩
  else none

theorem cayleyWithRoots?_eq {D : ℕ} {B C : CenteredRectangle} {roots : ℕ × ℕ}
    (h : cayleyWithRoots? D B roots = some C) : cayley? D B = some C := by
  dsimp only [cayleyWithRoots?] at h
  rcases Option.bind_eq_some.mp h with ⟨N, hN, h⟩
  rw [ScaledRectangle.norm?_eq hN] at h
  exact h

/-- Evaluate the inverse Cayley map with checked denominator norm roots. -/
def inverseCayleyWithRoots? (D : ℕ) (B : CenteredRectangle) (roots : ℕ × ℕ) :
    Option CenteredRectangle := do
  let one := ScaledRectangle.ofRat D 1
  let N ← ScaledRectangle.norm? D (B.center + one) roots
  let β := (N.fst : ℚ) / D
  if B.radius < β then
    let W ← ScaledRectangle.div? D (B.center - one) (B.center + one)
    return ⟨W, ScaledInterval.roundUp D (2 * B.radius / (β * (β - B.radius)))⟩
  else none

theorem inverseCayleyWithRoots?_eq {D : ℕ} {B C : CenteredRectangle}
    {roots : ℕ × ℕ} (h : inverseCayleyWithRoots? D B roots = some C) :
    inverseCayley? D B = some C := by
  dsimp only [inverseCayleyWithRoots?] at h
  rcases Option.bind_eq_some.mp h with ⟨N, hN, h⟩
  rw [ScaledRectangle.norm?_eq hN] at h
  exact h

/-- Evaluate the canonical quadratic argument with checked midpoint norm roots. -/
def affineSquareWithRoots? (D : ℕ) (d : ℚ) (B : CenteredRectangle)
    (roots : ℕ × ℕ) : Option CenteredRectangle := do
  let N ← ScaledRectangle.norm? D B.center roots
  return ⟨ScaledRectangle.ofRat D (1 - d) + ScaledRectangle.realMul D (ScaledInterval.ofRat D d)
      (ScaledRectangle.mul D B.center B.center),
    ScaledInterval.roundUp D (|d| * B.radius * (2 * ((N.snd : ℚ) / D) + B.radius))⟩

theorem affineSquareWithRoots?_eq {D : ℕ} {d : ℚ} {B C : CenteredRectangle}
    {roots : ℕ × ℕ} (h : affineSquareWithRoots? D d B roots = some C) :
    C = affineSquare D d B := by
  dsimp only [affineSquareWithRoots?] at h
  rcases Option.bind_eq_some.mp h with ⟨N, hN, h⟩
  rw [ScaledRectangle.norm?_eq hN] at h
  exact (Option.some.inj h).symm

/-- Evaluate centered principal roots with checked midpoint, whole-cell, and sum roots. -/
def sqrtWithRoots? (D : ℕ) (B : CenteredRectangle) (cert : RootCertificate) :
    Option CenteredRectangle := do
  let V ← ScaledRectangle.sqrtWithRoots? D B.center cert.center
  let W ← ScaledRectangle.sqrtWithRoots? D
    (ScaledRectangle.inflate ⌈(D : ℚ) * B.radius⌉ B.center) cert.wide
  let N ← ScaledRectangle.norm? D (W + V) cert.sumRoots
  let β := (N.fst : ℚ) / D
  if 0 < β then
    return ⟨V, ScaledInterval.roundUp D (B.radius / β)⟩
  else none

theorem sqrtWithRoots?_eq {D : ℕ} {B C : CenteredRectangle} {cert : RootCertificate}
    (h : sqrtWithRoots? D B cert = some C) : sqrt? D B = some C := by
  dsimp only [sqrtWithRoots?] at h
  rcases Option.bind_eq_some.mp h with ⟨V, hV, h⟩
  rcases Option.bind_eq_some.mp h with ⟨W, hW, h⟩
  rcases Option.bind_eq_some.mp h with ⟨N, hN, h⟩
  rw [ScaledRectangle.norm?_eq hN] at h
  dsimp only [sqrt?]
  exact Option.bind_eq_some.mpr ⟨V, ScaledRectangle.sqrtWithRoots?_eq hV,
    Option.bind_eq_some.mpr ⟨W, ScaledRectangle.sqrtWithRoots?_eq hW, h⟩⟩

end DirichletL.CenteredRectangle

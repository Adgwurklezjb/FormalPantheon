import Analysis.ScaledRootCertificate
import Analysis.ScaledRectangleChecked

/-!
Principal-root data for CDT's corrected contour, author Appendix A.4 page 204.
Complete meanings and branch checks precede these bodies in
-/

namespace DirichletL.ScaledRectangle

/-- Root proposals for the actual norm and selected principal-root component. -/
structure RootCertificate where
  /-- Roots of the lower and upper squared-norm radicands. -/
  normRoots : ℕ × ℕ
  /-- Roots of the lower and upper selected component radicands. -/
  componentRoots : ℕ × ℕ

/-- Check root data and retain every canonical principal-branch guard. -/
def sqrtWithRoots? (D : ℕ) (Z : ScaledRectangle) (cert : RootCertificate) :
    Option ScaledRectangle := do
  let N ← norm? D Z cert.normRoots
  if Z.1.snd < 0 then
    let V ← ScaledInterval.sqrt? D
      (ScaledInterval.mul D (ScaledInterval.rational D 1 2) (N - Z.1)) cert.componentRoots
    if 0 < V.fst then
      if 0 ≤ Z.2.fst then
        return (ScaledInterval.mul D (ScaledInterval.rational D 1 2)
          (ScaledInterval.mul D Z.2 (ScaledInterval.inv D V)), V)
      else if Z.2.snd < 0 then
        return (ScaledInterval.mul D (ScaledInterval.rational D 1 2)
          (ScaledInterval.mul D (-Z.2) (ScaledInterval.inv D V)), -V)
      else none
    else none
  else
    let V ← ScaledInterval.sqrt? D
      (ScaledInterval.mul D (ScaledInterval.rational D 1 2) (N + Z.1)) cert.componentRoots
    if 0 < V.fst then
      return (V, ScaledInterval.mul D (ScaledInterval.rational D 1 2)
        (ScaledInterval.mul D Z.2 (ScaledInterval.inv D V)))
    else none

theorem sqrtWithRoots?_eq {D : ℕ} {Z W : ScaledRectangle} {cert : RootCertificate}
    (h : sqrtWithRoots? D Z cert = some W) : sqrt? D Z = some W := by
  dsimp only [sqrtWithRoots?] at h
  rcases Option.bind_eq_some.mp h with ⟨N, hN, h⟩
  rw [norm?_eq hN] at h
  unfold sqrt?
  by_cases hz : Z.1.snd < 0
  · rw [if_pos hz] at h ⊢
    rcases Option.bind_eq_some.mp h with ⟨V, hV, h⟩
    have hv : V = sqrtImAbs D Z := ScaledInterval.sqrt?_eq hV
    subst V
    simpa only [sqrtOfNonnegIm, sqrtOfNegIm] using h
  · rw [if_neg hz] at h ⊢
    rcases Option.bind_eq_some.mp h with ⟨V, hV, h⟩
    have hv : V = sqrtRe D Z := ScaledInterval.sqrt?_eq hV
    subst V
    simpa only [sqrtOfRe] using h

end DirichletL.ScaledRectangle

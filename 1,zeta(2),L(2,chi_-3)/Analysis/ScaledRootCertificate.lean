import Analysis.ScaledRationalBounds

/-!
Checked integer-root data for CDT's interval certificate, corrected author Appendix A.4, page 204.
-/

namespace DirichletL.ScaledInterval

/-- Check a proposed natural root against the exact characterization of `Int.sqrt`. -/
def intSqrt? (n : ℤ) (root : ℕ) : Option ℤ :=
  if root * root ≤ n.toNat ∧ n.toNat < (root + 1) * (root + 1) then some (root : ℤ)
  else none

theorem intSqrt?_eq {n : ℤ} {root : ℕ} {r : ℤ}
    (h : intSqrt? n root = some r) : r = Int.sqrt n := by
  unfold intSqrt? at h
  split at h
  · rename_i hroot
    cases Option.some.inj h
    exact congrArg (fun k : ℕ => (k : ℤ)) (Nat.eq_sqrt.mpr hroot)
  · cases h

/-- Check both scaled radicands and retain the canonical outward upper increment. -/
def sqrt? (D : ℕ) (I : NonemptyInterval ℤ) (roots : ℕ × ℕ) :
    Option (NonemptyInterval ℤ) := do
  let l ← intSqrt? (I.fst * (D : ℤ)) roots.1
  let u ← intSqrt? (I.snd * (D : ℤ)) roots.2
  return NonemptyInterval.pure l ⊔ NonemptyInterval.pure (u + 1)

theorem sqrt?_eq {D : ℕ} {I J : NonemptyInterval ℤ} {roots : ℕ × ℕ}
    (h : sqrt? D I roots = some J) : J = sqrt D I := by
  dsimp only [sqrt?] at h
  rcases Option.bind_eq_some.mp h with ⟨l, hl, h⟩
  rcases Option.bind_eq_some.mp h with ⟨u, hu, h⟩
  cases Option.some.inj h
  rw [intSqrt?_eq hl, intSqrt?_eq hu]
  rfl

end DirichletL.ScaledInterval

namespace DirichletL.ScaledRectangle

/-- Check the two integer roots needed by the existing norm-squared rectangle. -/
def norm? (D : ℕ) (Z : ScaledRectangle) (roots : ℕ × ℕ) :
    Option (NonemptyInterval ℤ) := ScaledInterval.sqrt? D (normSq D Z) roots

theorem norm?_eq {D : ℕ} {Z : ScaledRectangle} {I : NonemptyInterval ℤ}
    {roots : ℕ × ℕ} (h : norm? D Z roots = some I) : I = norm D Z :=
  ScaledInterval.sqrt?_eq h

end DirichletL.ScaledRectangle

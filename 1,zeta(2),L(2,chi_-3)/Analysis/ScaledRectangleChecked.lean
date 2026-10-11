import Analysis.ScaledRectangleSqrt

/-!
Checked operations for CDT's lune and slit formulas, supplied TeX 9953-9964 and 10003-10019.
Meanings and inconclusive cases precede these bodies in
-/

namespace DirichletL.ScaledRectangle

/-- Divide only when the squared-norm enclosure has positive lower endpoint. -/
def div? (D : ℕ) (Z W : ScaledRectangle) : Option ScaledRectangle :=
  if 0 < (normSq D W).fst then some (div D Z W) else none

theorem div?_mem {D : ℕ} (hD : 0 < D) {Z W V : ScaledRectangle} {z w : ℂ}
    (hV : div? D Z W = some V) (hz : z ∈ denote D Z) (hw : w ∈ denote D W) :
    z / w ∈ denote D V := by
  unfold div? at hV
  split at hV
  · rename_i hW
    rcases Option.some.inj hV with rfl
    exact div_mem hD hW hz hw
  · cases hV

/-- Select a principal-root formula only after checking its integer endpoint guards. -/
def sqrt? (D : ℕ) (Z : ScaledRectangle) : Option ScaledRectangle :=
  if Z.1.snd < 0 then
    if 0 < (sqrtImAbs D Z).fst then
      if 0 ≤ Z.2.fst then some (sqrtOfNonnegIm D Z)
      else if Z.2.snd < 0 then some (sqrtOfNegIm D Z) else none
    else none
  else if 0 < (sqrtRe D Z).fst then some (sqrtOfRe D Z) else none

theorem sqrt?_mem {D : ℕ} (hD : 0 < D) {Z W : ScaledRectangle} {z : ℂ}
    (hW : sqrt? D Z = some W) (hz : z ∈ denote D Z) :
    z ^ (2⁻¹ : ℂ) ∈ denote D W := by
  unfold sqrt? at hW
  split at hW
  · split at hW
    · rename_i hB
      split at hW
      · rename_i hI
        rcases Option.some.inj hW with rfl
        exact sqrtOfNonnegIm_mem hD hB hI hz
      · split at hW
        · rename_i hI
          rcases Option.some.inj hW with rfl
          exact sqrtOfNegIm_mem hD hB hI hz
        · cases hW
    · cases hW
  · split at hW
    · rename_i hR
      rcases Option.some.inj hW with rfl
      exact sqrtOfRe_mem hD hR hz
    · cases hW

end DirichletL.ScaledRectangle

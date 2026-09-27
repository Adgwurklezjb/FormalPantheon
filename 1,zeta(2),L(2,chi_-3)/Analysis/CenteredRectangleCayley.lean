import Analysis.CenteredRectangleBasic
import Analysis.ScaledRectangleChecked
import Analysis.ContourCayleyVariation

/-!
Checked Cayley propagation for CDT v2's slit formula, supplied TeX 10003-10019.
Meanings and pole checks precede these bodies in
-/

namespace DirichletL.CenteredRectangle

/-- Evaluate the forward Cayley map after checking the whole-cell pole distance. -/
def cayley? (D : ℕ) (B : CenteredRectangle) : Option CenteredRectangle := do
  let one := ScaledRectangle.ofRat D 1
  let β := ScaledRectangle.normLower D (one - B.center)
  if B.radius < β then
    let W ← ScaledRectangle.div? D (one + B.center) (one - B.center)
    return ⟨W, ScaledInterval.roundUp D (2 * B.radius / (β * (β - B.radius)))⟩
  else none

theorem cayley?_encloses {D : ℕ} (hD : 0 < D)
    {B C : CenteredRectangle} {z z0 : ℂ}
    (hC : cayley? D B = some C) (h : Encloses D B z z0) :
    Encloses D C (cayleyMap z) (cayleyMap z0) := by
  have h1 : (1 : ℂ) ∈ ScaledRectangle.denote D (ScaledRectangle.ofRat D 1) := by
    simpa only [Rat.cast_one] using ScaledRectangle.ofRat_mem hD 1
  dsimp only [cayley?] at hC
  split at hC
  · rename_i hguard
    rcases Option.bind_eq_some.mp hC with ⟨W, hW, hC⟩
    cases Option.some.inj hC
    refine ⟨?_, ?_⟩
    · exact ScaledRectangle.div?_mem hD hW
        (ScaledRectangle.add_mem hD h1 h.1) (ScaledRectangle.sub_mem hD h1 h.1)
    · have hβ := ScaledRectangle.normLower_le_norm hD (ScaledRectangle.sub_mem hD h1 h.1)
      have hv := norm_cayleyMap_sub_le h.2 hβ (by exact_mod_cast hguard)
      apply hv.trans
      simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_sub] using
        ScaledInterval.le_roundUp hD
          (2 * B.radius / (ScaledRectangle.normLower D (ScaledRectangle.ofRat D 1 - B.center) *
            (ScaledRectangle.normLower D (ScaledRectangle.ofRat D 1 - B.center) - B.radius)))
  · cases hC

/-- Evaluate the inverse Cayley map after checking the whole-cell pole distance. -/
def inverseCayley? (D : ℕ) (B : CenteredRectangle) : Option CenteredRectangle := do
  let one := ScaledRectangle.ofRat D 1
  let β := ScaledRectangle.normLower D (B.center + one)
  if B.radius < β then
    let W ← ScaledRectangle.div? D (B.center - one) (B.center + one)
    return ⟨W, ScaledInterval.roundUp D (2 * B.radius / (β * (β - B.radius)))⟩
  else none

theorem inverseCayley?_encloses {D : ℕ} (hD : 0 < D)
    {B C : CenteredRectangle} {z z0 : ℂ}
    (hC : inverseCayley? D B = some C) (h : Encloses D B z z0) :
    Encloses D C (inverseCayleyMap z) (inverseCayleyMap z0) := by
  have h1 : (1 : ℂ) ∈ ScaledRectangle.denote D (ScaledRectangle.ofRat D 1) := by
    simpa only [Rat.cast_one] using ScaledRectangle.ofRat_mem hD 1
  dsimp only [inverseCayley?] at hC
  split at hC
  · rename_i hguard
    rcases Option.bind_eq_some.mp hC with ⟨W, hW, hC⟩
    cases Option.some.inj hC
    refine ⟨?_, ?_⟩
    · exact ScaledRectangle.div?_mem hD hW
        (ScaledRectangle.sub_mem hD h.1 h1) (ScaledRectangle.add_mem hD h.1 h1)
    · have hβ := ScaledRectangle.normLower_le_norm hD (ScaledRectangle.add_mem hD h.1 h1)
      have hv := norm_inverseCayleyMap_sub_le h.2 hβ (by exact_mod_cast hguard)
      apply hv.trans
      simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_sub] using
        ScaledInterval.le_roundUp hD
          (2 * B.radius / (ScaledRectangle.normLower D (B.center + ScaledRectangle.ofRat D 1) *
            (ScaledRectangle.normLower D (B.center + ScaledRectangle.ofRat D 1) - B.radius)))
  · cases hC

end DirichletL.CenteredRectangle

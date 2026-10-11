import Analysis.CenteredRectangleCayley
import Analysis.CenteredRectangleRoot
import Analysis.ContourLuneVariation

/-!
Centered slit and lune enclosures for CDT v2, supplied TeX 9953-9964 and 10003-10019.
-/

namespace DirichletL.CenteredRectangle

/-- Apply the Cayley map, quadratic argument, and checked principal square root. -/
def rootAfterCayley? (D : ℕ) (d : ℚ) (B : CenteredRectangle) : Option CenteredRectangle := do
  let C ← cayley? D B
  sqrt? D (affineSquare D d C)

theorem rootAfterCayley?_encloses {D : ℕ} (hD : 0 < D) (d : ℚ)
    {B C : CenteredRectangle} {z z0 : ℂ}
    (hC : rootAfterCayley? D d B = some C) (h : Encloses D B z z0) :
    Encloses D C (contourHalfPlaneRoot (d : ℝ) (cayleyMap z))
      (contourHalfPlaneRoot (d : ℝ) (cayleyMap z0)) := by
  rcases Option.bind_eq_some.mp hC with ⟨V, hV, hC⟩
  simpa only [contourHalfPlaneRoot, Complex.ofReal_ratCast] using
    sqrt?_encloses hD hC (affineSquare_encloses hD d (cayley?_encloses hD hV h))

/-- Evaluate a normalized slit using its exact rational quadratic coefficient. -/
def slit? (D : ℕ) (r : ℚ) (B : CenteredRectangle) : Option CenteredRectangle := do
  let K ← rootAfterCayley? D (4 * r / (1 + r) ^ 2) B
  inverseCayley? D K

theorem slit?_encloses {D : ℕ} (hD : 0 < D) (r : ℚ)
    {B C : CenteredRectangle} {z z0 : ℂ}
    (hC : slit? D r B = some C) (h : Encloses D B z z0) :
    Encloses D C (contourSlitMap (r : ℝ) z) (contourSlitMap (r : ℝ) z0) := by
  rcases Option.bind_eq_some.mp hC with ⟨K, hK, hC⟩
  simpa only [contourSlitMap, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_pow, Rat.cast_add, Rat.cast_one] using
    inverseCayley?_encloses hD hC (rootAfterCayley?_encloses hD _ hK h)

/-- Evaluate the lune map with its midpoint product and whole-cell variation bound. -/
def lune? (D : ℕ) (c : ℚ) (B : CenteredRectangle) : Option CenteredRectangle := do
  if 1 < c then
    let a := (c ^ 2 - 1) / (c ^ 2 + 1)
    let K ← rootAfterCayley? D (a ^ 2) B
    let one := ScaledRectangle.ofRat D 1
    let V ← ScaledRectangle.div? D (one - B.center) (ScaledRectangle.ofRat D (2 * a))
    let U := ScaledRectangle.normUpper D (one - B.center)
    let T := ScaledRectangle.normUpper D (K.center - one)
    return ⟨ScaledRectangle.mul D V (K.center - one),
      ScaledInterval.roundUp D (((U + B.radius) * K.radius + B.radius * T) / (2 * a))⟩
  else none

theorem lune?_encloses {D : ℕ} (hD : 0 < D) (c : ℚ)
    {B C : CenteredRectangle} {z z0 : ℂ}
    (hC : lune? D c B = some C) (h : Encloses D B z z0) :
    Encloses D C (contourLuneMap (c : ℝ) z) (contourLuneMap (c : ℝ) z0) := by
  dsimp only [lune?] at hC
  split at hC
  · rename_i hc
    rcases Option.bind_eq_some.mp hC with ⟨K, hK, hC⟩
    rcases Option.bind_eq_some.mp hC with ⟨V, hV, hC⟩
    cases Option.some.inj hC
    have hcr : (1 : ℝ) < c := by exact_mod_cast hc
    have ha := (lune_factor_mem_Ioo hcr).1
    have hk := rootAfterCayley?_encloses hD _ hK h
    simp only [Rat.cast_pow, Rat.cast_div, Rat.cast_sub, Rat.cast_one, Rat.cast_add] at hk
    have h1 : (1 : ℂ) ∈ ScaledRectangle.denote D (ScaledRectangle.ofRat D 1) := by
      simpa only [Rat.cast_one] using ScaledRectangle.ofRat_mem hD 1
    have hz0 := ScaledRectangle.sub_mem hD h1 h.1
    have hk0 := ScaledRectangle.sub_mem hD hk.1 h1
    constructor
    · have hv := ScaledRectangle.div?_mem hD hV hz0
        (ScaledRectangle.ofRat_mem hD (2 * ((c ^ 2 - 1) / (c ^ 2 + 1))))
      simpa only [contourLuneMap, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_div,
        Rat.cast_pow, Rat.cast_sub, Rat.cast_one, Rat.cast_add,
        Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_pow,
        Complex.ofReal_one, Complex.ofReal_ratCast] using ScaledRectangle.mul_mem hD hv hk0
    · have hδ0 : 0 ≤ (B.radius : ℝ) := (norm_nonneg _).trans h.2
      have hκ0 : 0 ≤ (K.radius : ℝ) := (norm_nonneg _).trans hk.2
      have hU := ScaledRectangle.norm_le_normUpper hD hz0
      have hT := ScaledRectangle.norm_le_normUpper hD hk0
      apply (norm_contourLuneMap_sub_le hcr h.2 hk.2).trans
      calc
        _ ≤ (((ScaledRectangle.normUpper D (ScaledRectangle.ofRat D 1 - B.center) : ℝ) +
            (B.radius : ℝ)) * (K.radius : ℝ) + (B.radius : ℝ) *
            (ScaledRectangle.normUpper D (K.center - ScaledRectangle.ofRat D 1) : ℝ)) /
            (2 * (((c : ℝ) ^ 2 - 1) / ((c : ℝ) ^ 2 + 1))) := by gcongr
        _ ≤ _ := by
          have hr := ScaledInterval.le_roundUp hD
            (((ScaledRectangle.normUpper D (ScaledRectangle.ofRat D 1 - B.center) + B.radius) *
                K.radius + B.radius *
                ScaledRectangle.normUpper D (K.center - ScaledRectangle.ofRat D 1)) /
              (2 * ((c ^ 2 - 1) / (c ^ 2 + 1))))
          push_cast at hr
          exact hr
  · cases hC

end DirichletL.CenteredRectangle

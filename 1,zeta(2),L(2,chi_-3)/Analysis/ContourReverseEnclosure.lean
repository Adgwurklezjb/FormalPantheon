import Analysis.ContourInputEnclosures
import Analysis.ScaledRationalBounds
import Analysis.ScaledRectangleRootCertificate
import Analysis.ContourReverseMap

/-!
Checked reverse expressions for CDT author Appendix A.4, pages 204-205.
Meanings and every division and branch guard precede the bodies in
-/

namespace DirichletL.ScaledRectangle

/-- Enclose the rational lune expression, checking its denominator. -/
def luneMap? (D : ℕ) (c : ℚ) (Z : ScaledRectangle) : Option ScaledRectangle :=
  let a := ofRat D (c ^ 2 + 1)
  let b := ofRat D (c ^ 2 - 1)
  div? D (mul D Z (a + mul D b Z)) (b + mul D a Z)

theorem luneMap?_mem {D : ℕ} (hD : 0 < D) (c : ℚ)
    {Z W : ScaledRectangle} {z : ℂ}
    (hW : luneMap? D c Z = some W) (hz : z ∈ denote D Z) :
    DirichletL.luneMap (c : ℂ) z ∈ denote D W := by
  have ha := ofRat_mem hD (c ^ 2 + 1)
  have hb := ofRat_mem hD (c ^ 2 - 1)
  have h := div?_mem hD hW (mul_mem hD hz (add_mem hD ha (mul_mem hD hb hz)))
    (add_mem hD hb (mul_mem hD ha hz))
  simpa only [DirichletL.luneMap, Rat.cast_add, Rat.cast_sub, Rat.cast_pow,
    Rat.cast_one] using h

/-- Enclose the total inverse slit, retaining the checked principal-root branch. -/
def contourSlitInverseWithRoots? (D : ℕ) (r : ℚ) (Z : ScaledRectangle)
    (cert : RootCertificate) : Option ScaledRectangle := do
  let one := ofRat D 1
  let d := (4 * r / (1 + r) ^ 2)⁻¹
  let U ← div? D (one + Z) (one - Z)
  let A := ofRat D (1 - d) + mul D (ofRat D d) (mul D U U)
  let R ← sqrtWithRoots? D A cert
  div? D (R - one) (R + one)

theorem contourSlitInverseWithRoots?_mem {D : ℕ} (hD : 0 < D) (r : ℚ)
    {Z W : ScaledRectangle} {z : ℂ} {cert : RootCertificate}
    (hW : contourSlitInverseWithRoots? D r Z cert = some W)
    (hz : z ∈ denote D Z) :
    contourSlitInverse (r : ℝ) z ∈ denote D W := by
  dsimp only [contourSlitInverseWithRoots?] at hW
  rcases Option.bind_eq_some.mp hW with ⟨U, hU, hW⟩
  rcases Option.bind_eq_some.mp hW with ⟨R, hR, hW⟩
  have h1 : (1 : ℂ) ∈ denote D (ofRat D 1) := by
    simpa only [Rat.cast_one] using ofRat_mem hD 1
  have hu := div?_mem hD hU (add_mem hD h1 hz) (sub_mem hD h1 hz)
  have ha := add_mem hD (ofRat_mem hD (1 - (4 * r / (1 + r) ^ 2)⁻¹))
    (mul_mem hD (ofRat_mem hD (4 * r / (1 + r) ^ 2)⁻¹) (mul_mem hD hu hu))
  have hr := sqrt?_mem hD (sqrtWithRoots?_eq hR) ha
  have hw := div?_mem hD hW (sub_mem hD hr h1) (add_mem hD hr h1)
  simpa only [contourSlitInverse, contourHalfPlaneRoot, cayleyMap, inverseCayleyMap,
    Rat.cast_sub, Rat.cast_inv, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_pow, Rat.cast_add, Rat.cast_one, Complex.ofReal_inv, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_pow, Complex.ofReal_add,
    Complex.ofReal_one, Complex.ofReal_ratCast, pow_two] using hw

/-- Evaluate the corrected reverse map using the four indexed slit-root certificates. -/
def cdtContourReverseWithRoots? (D : ℕ) (Q : ScaledRectangle)
    (cert : Fin 4 → RootCertificate) : Option ScaledRectangle := do
  let Z := mul D (ofRat D (-100 / 77)) Q
  let L ← luneMap? D (75 / 10) Z
  let R4 ← div? D (ofRat D (-1)) (rotation D (-783) 10000)
  let S4 ← contourSlitInverseWithRoots? D (772 / 1000) (mul D R4 L) (cert 3)
  let V3 ← div? D S4 (rotation D 3525 100000)
  let S3 ← contourSlitInverseWithRoots? D (55515 / 100000) V3 (cert 2)
  let V2 ← div? D S3 (rotation D 11543 100000)
  let S2 ← contourSlitInverseWithRoots? D (6188 / 10000) V2 (cert 1)
  let V1 ← div? D S2 (rotation D 7977 100000)
  contourSlitInverseWithRoots? D (91 / 100) V1 (cert 0)

theorem cdtContourReverseWithRoots?_mem {D : ℕ} (hD : 0 < D)
    {Q W : ScaledRectangle} {q : ℂ} {cert : Fin 4 → RootCertificate}
    (hW : cdtContourReverseWithRoots? D Q cert = some W)
    (hq : q ∈ denote D Q) : cdtContourReverseMap q ∈ denote D W := by
  dsimp only [cdtContourReverseWithRoots?] at hW
  rcases Option.bind_eq_some.mp hW with ⟨L, hL, hW⟩
  rcases Option.bind_eq_some.mp hW with ⟨R4, hR4, hW⟩
  rcases Option.bind_eq_some.mp hW with ⟨S4, hS4, hW⟩
  rcases Option.bind_eq_some.mp hW with ⟨V3, hV3, hW⟩
  rcases Option.bind_eq_some.mp hW with ⟨S3, hS3, hW⟩
  rcases Option.bind_eq_some.mp hW with ⟨V2, hV2, hW⟩
  rcases Option.bind_eq_some.mp hW with ⟨S2, hS2, hW⟩
  rcases Option.bind_eq_some.mp hW with ⟨V1, hV1, hW⟩
  have hrot4 := rotation_mem hD (-783) 10000 (by norm_num) (by norm_num [abs_div])
  have hrot3 := rotation_mem hD 3525 100000 (by norm_num) (by norm_num [abs_div])
  have hrot2 := rotation_mem hD 11543 100000 (by norm_num) (by norm_num [abs_div])
  have hrot1 := rotation_mem hD 7977 100000 (by norm_num) (by norm_num [abs_div])
  have hl := luneMap?_mem hD (75 / 10) hL (mul_mem hD (ofRat_mem hD (-100 / 77)) hq)
  have hr4 := div?_mem hD hR4 (ofRat_mem hD (-1)) hrot4
  have hs4 := contourSlitInverseWithRoots?_mem hD (772 / 1000) hS4 (mul_mem hD hr4 hl)
  have hv3 := div?_mem hD hV3 hs4 hrot3
  have hs3 := contourSlitInverseWithRoots?_mem hD (55515 / 100000) hS3 hv3
  have hv2 := div?_mem hD hV2 hs3 hrot2
  have hs2 := contourSlitInverseWithRoots?_mem hD (6188 / 10000) hS2 hv2
  have hv1 := div?_mem hD hV1 hs2 hrot1
  have hw := contourSlitInverseWithRoots?_mem hD (91 / 100) hW hv1
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one,
    Int.cast_ofNat, Int.cast_neg] at hw
  simpa only [cdtContourReverseMap, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_mul, Complex.ofReal_inv,
    div_eq_mul_inv, one_mul, neg_mul, mul_neg, mul_comm] using hw

theorem not_mem_image_cdtContourDiskMap_of_reverse_enclosure {D : ℕ}
    (hD : 0 < D) {W : ScaledRectangle} {q : ℂ}
    (hq : cdtContourReverseMap q ∈ denote D W)
    (hgap : (995 : ℤ) ^ 2 * (D : ℤ) <
      (1000 : ℤ) ^ 2 * (normSq D W).fst) :
    q ∉ cdtContourDiskMap '' Metric.closedBall (0 : ℂ) 1 := by
  apply not_mem_image_cdtContourDiskMap_of_reverse_norm
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hg : (995 : ℝ) ^ 2 * (D : ℝ) <
      (1000 : ℝ) ^ 2 * (normSq D W).fst := by exact_mod_cast hgap
  have hl := ((ScaledInterval.mem_denote_iff hD).mp (normSq_mem hD hq)).1
  rw [Complex.normSq_eq_norm_sq] at hl
  by_contra! hn
  have hs := pow_le_pow_left₀ (norm_nonneg (cdtContourReverseMap q)) hn 2
  have hm := mul_le_mul_of_nonneg_left hs hDr.le
  nlinarith

end DirichletL.ScaledRectangle

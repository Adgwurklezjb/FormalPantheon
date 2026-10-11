import Analysis.LogProfileErrorStep
import Analysis.CenteredRectangleBasic

/-!
Whole-cell level-two logarithmic profiles for CDT v2, TeX 6947-6948 and 8384-8404.
Meanings, exact rounding order, and the tail handoff precede these bodies in
-/

namespace DirichletL.CenteredRectangle

/-- The smaller of the global nome radius and the local center-plus-variation bound. -/
def profileNormBound (D : ℕ) (B : CenteredRectangle) : ℚ :=
  min (77 / 100) (ScaledInterval.roundUp D (ScaledRectangle.normUpper D B.center + B.radius))

theorem norm_le_profileNormBound {D : ℕ} (hD : 0 < D)
    {B : CenteredRectangle} {q q₀ : ℂ} (h : Encloses D B q q₀)
    (hq : ‖q‖ ≤ 77 / 100) (hq₀ : ‖q₀‖ ≤ 77 / 100) :
    ‖q‖ ≤ (profileNormBound D B : ℝ) ∧ ‖q₀‖ ≤ (profileNormBound D B : ℝ) := by
  have hδ0 : 0 ≤ (B.radius : ℝ) := (norm_nonneg _).trans h.2
  have hU := ScaledRectangle.norm_le_normUpper hD h.1
  have hround := ScaledInterval.le_roundUp hD (ScaledRectangle.normUpper D B.center + B.radius)
  simp only [Rat.cast_add] at hround
  simp only [profileNormBound, Rat.cast_min, Rat.cast_div, Rat.cast_ofNat]
  constructor
  · apply le_min hq
    apply le_trans ?_ hround
    calc
      ‖q‖ = ‖q₀ + (q - q₀)‖ := by congr 1; ring
      _ ≤ ‖q₀‖ + ‖q - q₀‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hU h.2
  · exact le_min hq₀ ((hU.trans (le_add_of_nonneg_right hδ0)).trans hround)

/-- Enclose the full signed logarithmic profile using 100 factors, variation, and the proved tail. -/
def logProfile? (D : ℕ) (B : CenteredRectangle) (kq kp : ℤ × ℤ) :
    Option (NonemptyInterval ℤ) := do
  let S ← LogProfileErrorState.iterate? D (profileNormBound D B) B.radius B.center 100
  let I ← LogProfileState.logPartial? D B.center S.profile kq kp
  let E := ScaledInterval.ofRat D (ScaledRectangle.normUpper D S.profile.slope * B.radius) +
    S.error + ScaledInterval.ofRat D (1 / 100000000)
  return ScaledInterval.inflate E.snd I

theorem logProfile?_mem {D : ℕ} (hD : 0 < D)
    {B : CenteredRectangle} {q q₀ : ℂ} (kq kp : ℤ × ℤ)
    {I : NonemptyInterval ℤ} (hI : logProfile? D B kq kp = some I)
    (h : Encloses D B q q₀) (hq : ‖q‖ ≤ 77 / 100) (hq₀ : ‖q₀‖ ≤ 77 / 100) :
    Real.log ‖levelTwoHauptmodul q‖ ∈ ScaledInterval.denote D I := by
  dsimp only [logProfile?] at hI
  rcases Option.bind_eq_some.mp hI with ⟨S, hS, hI⟩
  rcases Option.bind_eq_some.mp hI with ⟨J, hJ, hI⟩
  cases Option.some.inj hI
  have hρ := norm_le_profileNormBound hD h hq hq₀
  have hs := LogProfileErrorState.iterate?_interprets hD (profileNormBound D B) B.radius
    h.1 hρ.2 100 hS
  have hmid := LogProfileState.logPartial?_mem hD kq kp hJ h.1 hs.profile
    (hq₀.trans_lt (by norm_num : (77 / 100 : ℝ) < 1))
  have hU := ScaledRectangle.norm_le_normUpper hD hs.profile.2.2
  have hlin : |(levelTwoLogSlope 100 q₀ * (q - q₀)).re| ≤
      (ScaledRectangle.normUpper D S.profile.slope : ℝ) * (B.radius : ℝ) := by
    calc
      _ ≤ ‖levelTwoLogSlope 100 q₀ * (q - q₀)‖ := Complex.abs_re_le_norm _
      _ = ‖levelTwoLogSlope 100 q₀‖ * ‖q - q₀‖ := norm_mul _ _
      _ ≤ _ := mul_le_mul hU h.2 (norm_nonneg _) ((norm_nonneg _).trans hU)
  have hpartial : |levelTwoLogPartial 100 q - levelTwoLogPartial 100 q₀| ≤
      (ScaledRectangle.normUpper D S.profile.slope : ℝ) * (B.radius : ℝ) +
        (S.error.snd : ℝ) / D := by
    have heq : levelTwoLogPartial 100 q - levelTwoLogPartial 100 q₀ =
        (levelTwoLogSlope 100 q₀ * (q - q₀)).re + levelTwoLogRemainder 100 q q₀ := by
      dsimp only [levelTwoLogRemainder]
      ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add hlin (hs.remainder q hρ.1 h.2))
  have htail := abs_log_norm_levelTwoHauptmodul_sub_partial_100_lt (hs.nonzero q h.2) hq
  have hupper : (S.error.snd : ℝ) / D ∈ ScaledInterval.denote D S.error :=
    ⟨div_le_div_of_nonneg_right (by exact_mod_cast S.error.fst_le_snd)
      (Nat.cast_nonneg D), le_rfl⟩
  have he := (ScaledInterval.add_mem hD
    (ScaledInterval.add_mem hD
      (ScaledInterval.ofRat_mem hD (ScaledRectangle.normUpper D S.profile.slope * B.radius))
      hupper) (ScaledInterval.ofRat_mem hD (1 / 100000000))).2
  push_cast at he
  apply ScaledInterval.inflate_mem hD hmid
  calc
    _ ≤ |Real.log ‖levelTwoHauptmodul q‖ - levelTwoLogPartial 100 q| +
        |levelTwoLogPartial 100 q - levelTwoLogPartial 100 q₀| := abs_sub_le _ _ _
    _ ≤ 1 / 100000000 +
        ((ScaledRectangle.normUpper D S.profile.slope : ℝ) * (B.radius : ℝ) +
          (S.error.snd : ℝ) / D) := add_le_add htail.le hpartial
    _ = (ScaledRectangle.normUpper D S.profile.slope : ℝ) * (B.radius : ℝ) +
        (S.error.snd : ℝ) / D + 1 / 100000000 := by ring
    _ ≤ _ := he

end DirichletL.CenteredRectangle

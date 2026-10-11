import Arithmetic.BalancedSpecies
import Arithmetic.FlatDenominators
import Arithmetic.HorizontalDenominators
import Analysis.HolonomyOverflow

/-!
The common cap for balanced coefficient products in CDT v2, supplied
TeX 3770-3826, 4304-4404, and 4440-4518. Actual coefficient integrality,
degree windows, and coordinate bounds remain explicit hypotheses.
-/

namespace DirichletL

open Filter

/-- The two prefix factors of the perturbed coefficient multiplier. -/
noncomputable def cdtHolonomyPerturbedFlatMultiplier (ρ : ℝ) (i : Fin 14) (r : ℕ) : ℕ :=
  ∏ k ∈ Finset.range 2,
    lcmPrefix ⌊cdtDenominator14Perturbed ρ ((i : ℕ) + 1) (k + 1) * (r : ℝ)⌋₊

theorem cdtHolonomyPerturbedFlatMultiplier_eq (ρ : ℝ) (i : Fin 14) (r : ℕ) :
    cdtHolonomyPerturbedFlatMultiplier ρ i r =
      (if i ≠ 0 then lcmPrefix ⌊(2 + ρ) * (r : ℝ)⌋₊ else 1) *
        (if 3 ≤ (i : ℕ) then lcmPrefix ⌊(2 + ρ) * (r : ℝ)⌋₊ else 1) := by
  have htwo : (1 + ρ / 2) * 2 = 2 + ρ := by ring
  fin_cases i <;>
    simp [cdtHolonomyPerturbedFlatMultiplier, cdtDenominator14Perturbed,
      cdtDenominator14, Finset.prod_range_succ, htwo, lcmPrefix_zero]

theorem cdtHolonomyPerturbedMultiplier_factor (ρ : ℝ) (i : Fin 14) (r : ℕ) :
    cdtHolonomyPerturbedMultiplier ρ i r =
      r ^ cdtIntegrationExponents ((i : ℕ) + 1) *
        cdtHolonomyPerturbedFlatMultiplier ρ i r := rfl

theorem prod_cdtHolonomyPerturbedFlatMultiplier_dvd (h D : ℕ) {ρ δ : ℝ}
    (hρ : 0 ≤ 2 + ρ) (σ : ℕ → Fin 14)
    (hσ : ∀ i : Fin 14, ((Finset.univ : Finset (Fin (14 * h))).filter
      (fun j : Fin (14 * h) => σ (j : ℕ) = i)).card = h)
    (r : ℕ → ℕ) (hr : ∀ j < 14 * h,
      (r j : ℝ) ≤ (D : ℝ) * (δ + ((j : ℝ) + 1) / (h : ℝ))) :
    (∏ j ∈ Finset.range (14 * h), cdtHolonomyPerturbedFlatMultiplier ρ (σ j) (r j)) ∣
      cdt14FlatDenominator h D (2 + ρ) δ := by
  let s₁ := (Finset.univ : Finset (Fin (14 * h))).filter (fun j : Fin (14 * h) => σ (j : ℕ) ≠ 0)
  let s₂ := (Finset.univ : Finset (Fin (14 * h))).filter
    (fun j : Fin (14 * h) => 3 ≤ (σ (j : ℕ) : ℕ))
  have hp : (∏ j ∈ Finset.range (14 * h),
      cdtHolonomyPerturbedFlatMultiplier ρ (σ j) (r j)) =
      (∏ i ∈ s₁, lcmPrefix ⌊(2 + ρ) * (r (i : ℕ) : ℝ)⌋₊) *
        ∏ i ∈ s₂, lcmPrefix ⌊(2 + ρ) * (r (i : ℕ) : ℝ)⌋₊ := by
    rw [Finset.prod_range]
    simp only [cdtHolonomyPerturbedFlatMultiplier_eq, Finset.prod_mul_distrib,
      s₁, s₂, Finset.prod_filter]
  rw [hp]
  exact prod_lcmPrefix_dvd_cdt14FlatDenominator h D hρ s₁ s₂
    (card_cdt14_first_column_of_balanced σ hσ)
    (card_cdt14_second_column_of_balanced σ hσ) r hr

/-- A common natural clearing integer for the balanced coefficient products. -/
noncomputable def cdt14CoefficientDenominator (h D : ℕ) (ρ δ : ℝ) (n : ℕ → ℕ) : ℕ :=
  cdt14HorizontalDenominator (14 * h) D n * cdt14FlatDenominator h D (2 + ρ) δ

theorem cdt14CoefficientDenominator_pos (h D : ℕ) (ρ δ : ℝ) (n : ℕ → ℕ) :
    0 < cdt14CoefficientDenominator h D ρ δ n :=
  Nat.mul_pos (cdt14HorizontalDenominator_pos (14 * h) D n)
    (cdt14FlatDenominator_pos h D (2 + ρ) δ)

theorem isInteger_cdt14CoefficientDenominator_mul_prod (h D : ℕ) {ρ δ : ℝ}
    (hρ : 0 ≤ 2 + ρ) (σ : ℕ → Fin 14)
    (hσ : ∀ i : Fin 14, ((Finset.univ : Finset (Fin (14 * h))).filter
      (fun j : Fin (14 * h) => σ (j : ℕ) = i)).card = h)
    (n r : ℕ → ℕ) (q : ℕ → ℚ)
    (hn : ∀ j < 14 * h, (n j : ℝ) ≤ (D : ℝ) * (δ + ((j : ℝ) + 1) / (h : ℝ)))
    (hlo : ∀ j < 14 * h, n j - D ≤ r j) (hhi : ∀ j < 14 * h, r j ≤ n j)
    (hzero : ∀ j < 14 * h, r j = 0 → IsLocalization.IsInteger ℤ (q j))
    (hcoeff : ∀ j < 14 * h, IsLocalization.IsInteger ℤ
      ((cdtHolonomyPerturbedMultiplier ρ (σ j) (r j) : ℚ) * q j)) :
    IsLocalization.IsInteger ℤ
      ((cdt14CoefficientDenominator h D ρ δ n : ℚ) * ∏ j ∈ Finset.range (14 * h), q j) := by
  let a : ℕ → ℕ := fun j => cdtHolonomyPerturbedFlatMultiplier ρ (σ j) (r j)
  let e : ℕ → ℕ := fun j => cdtIntegrationExponents ((σ j : ℕ) + 1)
  let f : ℕ → ℚ := fun j => (a j : ℚ) * q j
  have he (j : ℕ) (_ : j < 14 * h) : e j ≤ 1 := by
    dsimp only [e, cdtIntegrationExponents]
    split_ifs <;> norm_num
  have hsum : (∑ j ∈ Finset.range (14 * h), e j) ≤ 3 * (14 * h) / 7 := by
    have hs := sum_cdt14_exponents_of_balanced σ hσ
    dsimp only [e]
    rw [hs]
    omega
  have hz (j : ℕ) (hj : j < 14 * h) (hrj : r j = 0) :
      IsLocalization.IsInteger ℤ (f j) :=
    IsLocalization.isInteger_mul ⟨(a j : ℤ), by simp⟩ (hzero j hj hrj)
  have hc (j : ℕ) (hj : j < 14 * h) :
      IsLocalization.IsInteger ℤ ((r j : ℚ) ^ e j * f j) := by
    simpa only [cdtHolonomyPerturbedMultiplier_factor, Nat.cast_mul, Nat.cast_pow,
      mul_assoc, a, e, f] using hcoeff j hj
  have hclear := isInteger_cdt14HorizontalDenominator_mul_prod (14 * h) D n r e f
    hlo hhi he hsum hz hc
  have hclear' : IsLocalization.IsInteger ℤ
      (((cdt14HorizontalDenominator (14 * h) D n *
        ∏ j ∈ Finset.range (14 * h), a j : ℕ) : ℚ) *
          ∏ j ∈ Finset.range (14 * h), q j) := by
    simpa only [f, Finset.prod_mul_distrib, Nat.cast_mul, Nat.cast_prod,
      mul_assoc] using hclear
  have hflat := prod_cdtHolonomyPerturbedFlatMultiplier_dvd h D hρ σ hσ r
    (fun j hj => (by exact_mod_cast hhi j hj : (r j : ℝ) ≤ n j).trans (hn j hj))
  exact isInteger_nat_mul_of_dvd hclear' (mul_dvd_mul dvd_rfl hflat)

theorem log_cdt14CoefficientDenominator (h D : ℕ) (ρ δ : ℝ) (n : ℕ → ℕ) :
    Real.log (cdt14CoefficientDenominator h D ρ δ n : ℝ) =
      Real.log (cdt14HorizontalDenominator (14 * h) D n : ℝ) +
        Real.log (cdt14FlatDenominator h D (2 + ρ) δ : ℝ) := by
  rw [cdt14CoefficientDenominator, Nat.cast_mul, Real.log_mul
    (by exact_mod_cast (cdt14HorizontalDenominator_pos (14 * h) D n).ne')
    (by exact_mod_cast (cdt14FlatDenominator_pos h D (2 + ρ) δ).ne')]

theorem exists_delta_eventually_log_cdt14CoefficientDenominator_le {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ₀ δ₀ : ℝ, 0 < ρ₀ ∧ 0 < δ₀ ∧ ∀ᶠ h : ℕ in atTop, ∀ᶠ D : ℕ in atTop,
      ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ ρ₀ → ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ₀ → ∀ n : ℕ → ℕ,
        (∀ j < 14 * h, (n j : ℝ) ≤ (D : ℝ) * (δ + ((j : ℝ) + 1) / (h : ℝ))) →
        Real.log (cdt14CoefficientDenominator h D ρ δ n : ℝ) ≤
          98 * (h : ℝ) * (D : ℝ) * ((16603 / 3920 : ℝ) + ε) := by
  obtain ⟨δH, hδH, hH⟩ := exists_delta_eventually_log_cdt14HorizontalDenominator_le (half_pos hε)
  obtain ⟨ρF, δF, hρF, hδF, hF⟩ :=
    exists_delta_eventually_log_cdt14FlatDenominator_le (half_pos hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hH
  refine ⟨ρF, min δF δH, hρF, lt_min hδF hδH, ?_⟩
  filter_upwards [hF, eventually_ge_atTop N, eventually_gt_atTop (0 : ℕ)] with h hFh hNh hh
  filter_upwards [hFh, hN (14 * h) (by omega)] with D hFD hHD ρ hρ0 hρ δ hδ0 hδ n hn
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hgrid (j : ℕ) : δ + 14 * ((j : ℝ) + 1) / ((14 * h : ℕ) : ℝ) =
      δ + ((j : ℝ) + 1) / (h : ℝ) := by
    push_cast
    field_simp [hhR]
  have hHn := hHD δ hδ0 (hδ.trans (min_le_right _ _)) n (by
    intro j hj
    simpa only [hgrid] using hn j hj)
  have hFn := hFD ρ hρ0 hρ δ hδ0 (hδ.trans (min_le_left _ _))
  have hHn' : Real.log (cdt14HorizontalDenominator (14 * h) D n : ℝ) ≤
      98 * (h : ℝ) * (D : ℝ) * ((27 / 80 : ℝ) + ε / 2) := by
    convert hHn using 1
    push_cast
    ring
  rw [log_cdt14CoefficientDenominator]
  calc
    _ ≤ 98 * (h : ℝ) * (D : ℝ) * ((27 / 80 : ℝ) + ε / 2) +
        98 * (h : ℝ) * (D : ℝ) * ((191 / 49 : ℝ) + ε / 2) := add_le_add hHn' hFn
    _ = _ := by ring

end DirichletL

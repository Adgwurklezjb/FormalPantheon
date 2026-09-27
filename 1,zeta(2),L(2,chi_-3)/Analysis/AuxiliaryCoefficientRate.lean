import Arithmetic.AuxiliaryCoefficientBounds

/-!
The logarithmic denominator rate for actual auxiliary coefficients in CDT v2,
supplied TeX 4304-4404 and 4440-4518. The fixed multiplier, strict cutoff,
and parameter order are checked before the proof in
-/

namespace DirichletL

open Filter

theorem exists_epsilon_eventually_neg_log_abs_cdtAuxiliary_coeff_le
    (a b c : ℤ) {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ᶠ h : ℕ in atTop, ∀ᶠ D : ℕ in atTop,
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ δ : ℝ, 0 < δ → δ < ε → ∀ L : ℕ,
        (L : ℝ) ≤ (14 + δ) * D + 1 →
        ∀ (t : ↥(auxiliaryFreeIndices 14 h D ε) → ℤ) (n : Fin (14 * h) →₀ ℕ),
        (∀ j, n j < L) →
        HasIntervalDiscrepancyLE (fun j => (n j : ℝ) / ((14 + δ) * D)) ε →
        MvPowerSeries.coeff (R := ℚ) n (auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε t) ≠ 0 →
        -Real.log |(MvPowerSeries.coeff (R := ℚ) n
          (auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε t) : ℝ)| ≤
          98 * (h : ℝ) * D * ((16603 / 3920 : ℝ) + η) := by
  obtain ⟨ρ, δ₀, hρ, hδ₀, hcap⟩ :=
    exists_delta_eventually_log_cdt14CoefficientDenominator_le (half_pos hη)
  obtain ⟨M, hM, hclear⟩ := exists_int_pow_cdtAuxiliary_coeff_denominators a b c hρ
  obtain ⟨T, hT⟩ := exists_nat_gt (Real.log |(M : ℝ)| / (7 * (η / 2)))
  refine ⟨min 1 (δ₀ / 16), lt_min (by norm_num) (div_pos hδ₀ (by norm_num)),
    min_le_left _ _, ?_⟩
  filter_upwards [hcap, eventually_gt_atTop (0 : ℕ)] with h hcapH hh
  filter_upwards [hcapH, eventually_gt_atTop (0 : ℕ), eventually_ge_atTop T] with D hcapD hD hTD
  intro ε hε hε₀ δ hδ hδε L hLR t n hn hdis hβ
  have hε1 : ε ≤ 1 := hε₀.trans (min_le_left _ _)
  obtain ⟨σ, _, hncap⟩ := exists_sorted_auxiliary_exponent_cap hh hD hδ hδε hε1
    (fun j => n j) hn hLR hdis
  let n' : ℕ → ℕ := Function.extend Fin.val (fun j => n (σ j)) (fun _ => 0)
  have he (j : Fin (14 * h)) : n' j = n (σ j) := Fin.val_injective.extend_apply _ _ j
  have hn' (j : ℕ) (hj : j < 14 * h) :
      (n' j : ℝ) ≤ D * (16 * ε + ((j : ℝ) + 1) / h) := by
    change (n' (⟨j, hj⟩ : Fin (14 * h)) : ℝ) ≤ _
    rw [he]
    exact hncap ⟨j, hj⟩
  have hsmall : 16 * ε ≤ δ₀ := by
    have hs := hε₀.trans (min_le_right 1 (δ₀ / 16))
    linarith
  have hNlog := hcapD ρ hρ.le le_rfl (16 * ε) (by positivity) hsmall n' hn'
  have hβlog := neg_log_abs_le_of_isInteger_nat_mul_int_pow
    (cdt14CoefficientDenominator h D ρ (16 * ε) n') M (14 * h)
    (MvPowerSeries.coeff (R := ℚ) n (auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε t))
    (cdt14CoefficientDenominator_pos h D ρ (16 * ε) n') hM hβ
    (hclear h D ε (16 * ε) t n σ hncap)
  have hquot : Real.log |(M : ℝ)| / (7 * (η / 2)) ≤ (D : ℝ) :=
    hT.le.trans (by exact_mod_cast hTD)
  have hDM : Real.log |(M : ℝ)| ≤ (D : ℝ) * (7 * (η / 2)) :=
    (div_le_iff₀ (by positivity : 0 < 7 * (η / 2))).mp hquot
  have hMterm : ((14 * h : ℕ) : ℝ) * Real.log |(M : ℝ)| ≤
      98 * (h : ℝ) * D * (η / 2) := by
    calc
      _ = (14 * (h : ℝ)) * Real.log |(M : ℝ)| := by push_cast; ring
      _ ≤ (14 * (h : ℝ)) * ((D : ℝ) * (7 * (η / 2))) :=
        mul_le_mul_of_nonneg_left hDM (by positivity)
      _ = _ := by ring
  calc
    _ ≤ Real.log (cdt14CoefficientDenominator h D ρ (16 * ε) n' : ℝ) +
        ((14 * h : ℕ) : ℝ) * Real.log |(M : ℝ)| := hβlog
    _ ≤ 98 * (h : ℝ) * D * ((16603 / 3920 : ℝ) + η / 2) +
        98 * (h : ℝ) * D * (η / 2) := add_le_add hNlog hMterm
    _ = _ := by ring

end DirichletL

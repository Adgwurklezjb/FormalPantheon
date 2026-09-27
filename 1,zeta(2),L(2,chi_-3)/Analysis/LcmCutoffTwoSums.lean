import Analysis.LcmCutoffTwoIntegral
import Analysis.MonotoneIntegralSums
import Arithmetic.LcmIntervalQuotientScaling

/-!
Uniform finite horizontal sums in CDT v2, supplied TeX 4480-4518.
The exact quotient is estimated at the actual natural coordinate;
only its continuous main rate is compared with the real grid.
-/

namespace DirichletL

open Filter MeasureTheory

theorem integral_lcmCutoffTwoRate_shift_le {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ t in δ..δ + 14, lcmCutoffTwoRate 7 t) ≤
      (843 / 40 : ℝ) + δ * (harmonic 7 : ℝ) := by
  have hc := continuous_lcmCutoffTwoRate 7
  have henlarge : (∫ t in δ..δ + 14, lcmCutoffTwoRate 7 t) ≤
      ∫ t in (0 : ℝ)..14 + δ, lcmCutoffTwoRate 7 t :=
    intervalIntegral.integral_mono_interval hδ (by linarith) (by linarith)
      (Filter.Eventually.of_forall (lcmCutoffTwoRate_nonneg 7))
      (hc.intervalIntegrable 0 (14 + δ))
  have htail : (∫ t in (14 : ℝ)..14 + δ, lcmCutoffTwoRate 7 t) ≤
      δ * (harmonic 7 : ℝ) := by
    have h := intervalIntegral.integral_mono (μ := volume)
      (g := fun _ : ℝ => (harmonic 7 : ℝ)) (by linarith : (14 : ℝ) ≤ 14 + δ)
      (hc.intervalIntegrable 14 (14 + δ)) intervalIntegrable_const
      (lcmCutoffTwoRate_le_harmonic 7)
    simpa only [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul] using h
  have hadd : (∫ t in (0 : ℝ)..14, lcmCutoffTwoRate 7 t) +
      (∫ t in (14 : ℝ)..14 + δ, lcmCutoffTwoRate 7 t) =
        ∫ t in (0 : ℝ)..14 + δ, lcmCutoffTwoRate 7 t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 14) (hc.intervalIntegrable 14 (14 + δ))
  rw [integral_lcmCutoffTwoRate_seven_fourteen] at hadd
  linarith only [henlarge, htail, hadd]

theorem sum_lcmCutoffTwoRate_grid_le {d : ℕ} (hd : 0 < d) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∑ j ∈ Finset.range d,
      lcmCutoffTwoRate 7 (δ + 14 * ((j : ℝ) + 1) / (d : ℝ))) / (d : ℝ) ≤
        (843 / 560 : ℝ) + δ * (harmonic 7 : ℝ) / 14 + (harmonic 7 : ℝ) / (d : ℝ) := by
  have hgrid := sum_right_grid_le_integral (monotone_lcmCutoffTwoRate 7) δ
    (by norm_num : (0 : ℝ) < 14) hd
  have hint := div_le_div_of_nonneg_right (integral_lcmCutoffTwoRate_shift_le hδ)
    (by norm_num : (0 : ℝ) ≤ 14)
  have hend : lcmCutoffTwoRate 7 (δ + 14) - lcmCutoffTwoRate 7 δ ≤ (harmonic 7 : ℝ) := by
    linarith only [lcmCutoffTwoRate_le_harmonic 7 (δ + 14), lcmCutoffTwoRate_nonneg 7 δ]
  have he := div_le_div_of_nonneg_right hend (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  linarith only [hgrid, hint, he]

theorem eventually_log_lcmIntervalQuotient_prod_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ D : ℕ in atTop, ∀ d : ℕ, 0 < d → ∀ δ : ℝ, 0 ≤ δ → δ ≤ 2 →
      ∀ n : ℕ → ℕ,
        (∀ j < d, (n j : ℝ) ≤ (D : ℝ) * (δ + 14 * ((j : ℝ) + 1) / (d : ℝ))) →
        Real.log ((∏ j ∈ Finset.range d, lcmIntervalQuotient (n j) D (2 * D) : ℕ) : ℝ) ≤
          (d : ℝ) * (D : ℝ) * ((843 / 560 : ℝ) + δ * (harmonic 7 : ℝ) / 14 +
            (harmonic 7 : ℝ) / (d : ℝ) + η) := by
  filter_upwards [eventually_abs_log_lcmIntervalQuotient_cutoff_two_le 7 hη,
    eventually_gt_atTop (0 : ℕ)] with D hD hD0 d hd δ hδ0 hδ2 n hn
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD0
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hpoint (j : ℕ) (hj : j ∈ Finset.range d) :
      Real.log (lcmIntervalQuotient (n j) D (2 * D) : ℝ) ≤
        (D : ℝ) * lcmCutoffTwoRate 7 (δ + 14 * ((j : ℝ) + 1) / (d : ℝ)) + η * (D : ℝ) := by
    have hjd : j < d := Finset.mem_range.mp hj
    have hjR : (j : ℝ) + 1 ≤ d := by exact_mod_cast Nat.succ_le_of_lt hjd
    have hfrac : ((j : ℝ) + 1) / (d : ℝ) ≤ 1 :=
      (div_le_iff₀ hdR).mpr (by simpa only [one_mul] using hjR)
    have hgrid : δ + 14 * ((j : ℝ) + 1) / (d : ℝ) ≤ 16 := by
      have h := mul_le_mul_of_nonneg_left hfrac (by norm_num : (0 : ℝ) ≤ 14)
      rw [← mul_div_assoc] at h
      linarith only [h, hδ2]
    have hnR : (n j : ℝ) ≤ 16 * (D : ℝ) :=
      (hn j hjd).trans (by nlinarith only [mul_le_mul_of_nonneg_left hgrid hDR.le])
    have hnN : n j ≤ (2 * 7 + 2) * D := by exact_mod_cast hnR
    have hratio : (n j : ℝ) / (D : ℝ) ≤ δ + 14 * ((j : ℝ) + 1) / (d : ℝ) :=
      (div_le_iff₀ hDR).mpr (by simpa only [mul_comm] using hn j hjd)
    have he := (abs_le.mp (hD (n j) hnN)).2
    have hr := mul_le_mul_of_nonneg_left (monotone_lcmCutoffTwoRate 7 hratio) hDR.le
    linarith only [he, hr]
  have hsum := (div_le_iff₀ hdR).mp (sum_lcmCutoffTwoRate_grid_le hd hδ0)
  have hscaled := mul_le_mul_of_nonneg_left hsum hDR.le
  calc
    _ = ∑ j ∈ Finset.range d, Real.log (lcmIntervalQuotient (n j) D (2 * D) : ℝ) := by
      rw [Nat.cast_prod, Real.log_prod _ _ (fun j _ => by
        exact_mod_cast (lcmIntervalQuotient_pos (n j) D (2 * D)).ne')]
    _ ≤ ∑ j ∈ Finset.range d,
        ((D : ℝ) * lcmCutoffTwoRate 7 (δ + 14 * ((j : ℝ) + 1) / (d : ℝ)) + η * (D : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ = (D : ℝ) * (∑ j ∈ Finset.range d,
        lcmCutoffTwoRate 7 (δ + 14 * ((j : ℝ) + 1) / (d : ℝ))) + (d : ℝ) * (η * (D : ℝ)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ _ := by nlinarith only [hscaled]

end DirichletL

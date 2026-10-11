import Analysis.PowerSeriesAnalytic

/-!
Convergent evaluation of rational formal series and their products.
Mathlib's Cauchy product supplies the multiplication identity; absolute
summability here uses the finite-dimensional complex codomain.
-/

namespace DirichletL

open Filter
open scoped Topology NNReal ENNReal

theorem sum_complexSeries_eq_of_hasSum {p : PowerSeries ℚ} {z a : ℂ}
    (h : HasSum (fun n => (PowerSeries.coeff (R := ℚ) n p : ℂ) * z ^ n) a) :
    (complexSeries p).sum z = a := by
  change FormalMultilinearSeries.ofScalarsSum
    (fun n => (PowerSeries.coeff (R := ℚ) n p : ℂ)) z = a
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simpa only [smul_eq_mul] using h.tsum_eq

theorem norm_le_radius_complexSeries_of_hasSum {p : PowerSeries ℚ} {z a : ℂ}
    (h : HasSum (fun n => (PowerSeries.coeff (R := ℚ) n p : ℂ) * z ^ n) a) :
    (‖z‖₊ : ℝ≥0∞) ≤ (complexSeries p).radius := by
  apply (complexSeries p).le_radius_of_summable_norm
  simpa only [FormalMultilinearSeries.norm_apply_eq_norm_coef, coeff_complexSeries,
    coe_nnnorm, norm_mul, norm_pow] using h.summable.norm

theorem eventually_hasSum_of_hasFPowerSeriesAt {p : PowerSeries ℚ} {f : ℂ → ℂ}
    (h : HasFPowerSeriesAt f (complexSeries p) 0) :
    ∀ᶠ z : ℂ in 𝓝 0, HasSum (fun n => (PowerSeries.coeff (R := ℚ) n p : ℂ) * z ^ n) (f z) := by
  simpa [complexSeries, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using
    h.eventually_hasSum_sub

theorem pos_radius_complexSeries_of_eventually_hasSum {p : PowerSeries ℚ} {f : ℂ → ℂ}
    (h : ∀ᶠ z : ℂ in 𝓝 0,
      HasSum (fun n => (PowerSeries.coeff (R := ℚ) n p : ℂ) * z ^ n) (f z)) :
    0 < (complexSeries p).radius := by
  have hn : ∀ᶠ z : ℂ in 𝓝[≠] 0, z ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hz
  obtain ⟨z, hz, hz0⟩ := ((h.filter_mono nhdsWithin_le_nhds).and hn).exists
  have hp : (0 : ℝ≥0∞) < ‖z‖₊ := by
    rw [ENNReal.coe_pos, nnnorm_pos]
    exact hz0
  exact hp.trans_le (norm_le_radius_complexSeries_of_hasSum hz)

/-- The formal Cauchy product evaluates to the product of the two convergent sums. -/
theorem hasSum_powerSeries_mul {p q : PowerSeries ℚ} {z a b : ℂ}
    (hp : HasSum (fun n => (PowerSeries.coeff (R := ℚ) n p : ℂ) * z ^ n) a)
    (hq : HasSum (fun n => (PowerSeries.coeff (R := ℚ) n q : ℂ) * z ^ n) b) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n (p * q) : ℂ) * z ^ n) (a * b) := by
  have hn := summable_norm_sum_mul_antidiagonal_of_summable_norm hp.summable.norm hq.summable.norm
  have hs := hn.of_norm.hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    hp.summable.norm hq.summable.norm, hp.tsum_eq, hq.tsum_eq] at hs
  convert hs using 1
  ext n
  rw [PowerSeries.coeff_mul, Rat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [Rat.cast_mul, ← Finset.mem_antidiagonal.mp hij, pow_add]
  ring

end DirichletL

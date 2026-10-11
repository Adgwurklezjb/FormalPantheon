import Analysis.ThetaSummation

/-!
Complex evaluation and unit-disk convergence of the integer theta series
used for CDT v2 Section 11.1. The coefficient series are the existing
formal definitions, and the analytic functions are Mathlib's theta functions.
-/

namespace DirichletL

open Function.Periodic
open scoped NNReal ENNReal Real

private theorem hasSum_map_int_sparse {e : ℕ ↪ ℕ} {c : ℕ → ℤ} {z a : ℂ}
    (h : HasSum (fun i => (c i : ℂ) * z ^ e i) a) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n
      (PowerSeries.map (Int.castRingHom ℚ) (sparsePowerSeries e c)) : ℂ) * z ^ n) a := by
  rw [map_sparsePowerSeries]
  exact hasSum_sparsePowerSeries_eval e _ (by simpa using h)

private theorem hasSum_coeff_two_mul_sub_one {p : PowerSeries ℚ} {z a : ℂ}
    (h : HasSum (fun n => (PowerSeries.coeff (R := ℚ) n p : ℂ) * z ^ n) a) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n (2 * p - 1) : ℂ) * z ^ n) (2 * a - 1) := by
  simpa only [two_mul, map_sub, map_add, Rat.cast_sub, Rat.cast_add, sub_mul, add_mul] using
    (h.add h).sub (hasSum_powerSeries_one z)

theorem hasSum_thetaThreeSeries_qParam {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n
      (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries) : ℂ) * qParam 1 τ ^ n)
      (jacobiTheta (2 * τ)) := by
  have hs := hasSum_map_int_sparse (e := natSquareEmbedding) (c := fun _ => 1)
    (by simpa using hasSum_qParam_square hτ)
  have he : 2 * ((jacobiTheta (2 * τ) + 1) / 2) - 1 = jacobiTheta (2 * τ) := by ring
  simpa only [thetaThreeSeries, map_sub, map_mul, map_ofNat, map_one, he] using
    hasSum_coeff_two_mul_sub_one hs

theorem hasSum_thetaFourSeries_qParam {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n
      (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries) : ℂ) * qParam 1 τ ^ n)
      (jacobiTheta₂ (1 / 2) (2 * τ)) := by
  have hs := hasSum_map_int_sparse (e := natSquareEmbedding) (c := fun n => (-1) ^ n)
    (by simpa only [natSquareEmbedding_apply, Int.cast_pow, Int.cast_neg, Int.cast_one]
      using hasSum_neg_one_pow_mul_qParam_square hτ)
  have he : 2 * ((jacobiTheta₂ (1 / 2) (2 * τ) + 1) / 2) - 1 =
      jacobiTheta₂ (1 / 2) (2 * τ) := by ring
  simpa only [thetaFourSeries, map_sub, map_mul, map_ofNat, map_one, he] using
    hasSum_coeff_two_mul_sub_one hs

theorem hasSum_thetaTwoNormalizedSeries_qParam {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n
      (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries) : ℂ) * qParam 1 τ ^ n)
      (jacobiTheta₂ τ (2 * τ)) := by
  have hs := hasSum_map_int_sparse (e := natPronicEmbedding) (c := fun _ => 1)
    (by simpa using hasSum_qParam_pronic hτ)
  simpa only [thetaTwoNormalizedSeries, two_mul, map_add, Rat.cast_add, add_mul, add_halves]
    using hs.add hs

theorem sum_complexSeries_thetaThreeSeries_qParam {τ : ℂ} (hτ : 0 < τ.im) :
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum (qParam 1 τ) =
      jacobiTheta (2 * τ) :=
  sum_complexSeries_eq_of_hasSum (hasSum_thetaThreeSeries_qParam hτ)

theorem sum_complexSeries_thetaFourSeries_qParam {τ : ℂ} (hτ : 0 < τ.im) :
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum (qParam 1 τ) =
      jacobiTheta₂ (1 / 2) (2 * τ) :=
  sum_complexSeries_eq_of_hasSum (hasSum_thetaFourSeries_qParam hτ)

theorem sum_complexSeries_thetaTwoNormalizedSeries_qParam {τ : ℂ} (hτ : 0 < τ.im) :
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)).sum
      (qParam 1 τ) = jacobiTheta₂ τ (2 * τ) :=
  sum_complexSeries_eq_of_hasSum (hasSum_thetaTwoNormalizedSeries_qParam hτ)

private theorem one_le_radius_of_qParam_summable {p : PowerSeries ℚ}
    (h : ∀ τ : ℂ, 0 < τ.im →
      Summable (fun n => (PowerSeries.coeff (R := ℚ) n p : ℂ) * qParam 1 τ ^ n)) :
    1 ≤ (complexSeries p).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  by_cases hr0 : r = 0
  · subst r
    simp
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hr0 : 0 < r)
  have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr
  have hz : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hrpos)
  have hnorm : ‖(r : ℂ)‖ < 1 := by simpa using hr1
  have hτ := im_invQParam_pos_of_norm_lt_one (by norm_num : (0 : ℝ) < 1) hnorm hz
  have hs : Summable (fun n => (PowerSeries.coeff (R := ℚ) n p : ℂ) * (r : ℂ) ^ n) := by
    simpa only [qParam_right_inv (by norm_num : (1 : ℝ) ≠ 0) hz] using
      h (invQParam 1 (r : ℂ)) hτ
  simpa only [Complex.nnnorm_real, Real.nnnorm_of_nonneg r.coe_nonneg] using
    norm_le_radius_complexSeries_of_hasSum hs.hasSum

theorem one_le_radius_complexSeries_thetaThreeSeries :
    1 ≤ (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).radius :=
  one_le_radius_of_qParam_summable fun _ hτ => (hasSum_thetaThreeSeries_qParam hτ).summable

theorem one_le_radius_complexSeries_thetaFourSeries :
    1 ≤ (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).radius :=
  one_le_radius_of_qParam_summable fun _ hτ => (hasSum_thetaFourSeries_qParam hτ).summable

theorem one_le_radius_complexSeries_thetaTwoNormalizedSeries :
    1 ≤ (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)).radius :=
  one_le_radius_of_qParam_summable fun _ hτ =>
    (hasSum_thetaTwoNormalizedSeries_qParam hτ).summable

theorem hasFPowerSeriesOnBall_thetaThreeSeries :
    HasFPowerSeriesOnBall
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)) 0 1 :=
  ((complexSeries _).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le one_le_radius_complexSeries_thetaThreeSeries)).mono
      zero_lt_one one_le_radius_complexSeries_thetaThreeSeries

theorem hasFPowerSeriesOnBall_thetaFourSeries :
    HasFPowerSeriesOnBall
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)) 0 1 :=
  ((complexSeries _).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le one_le_radius_complexSeries_thetaFourSeries)).mono
      zero_lt_one one_le_radius_complexSeries_thetaFourSeries

theorem hasFPowerSeriesOnBall_thetaTwoNormalizedSeries :
    HasFPowerSeriesOnBall
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)).sum
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)) 0 1 :=
  ((complexSeries _).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le one_le_radius_complexSeries_thetaTwoNormalizedSeries)).mono
      zero_lt_one one_le_radius_complexSeries_thetaTwoNormalizedSeries

end DirichletL

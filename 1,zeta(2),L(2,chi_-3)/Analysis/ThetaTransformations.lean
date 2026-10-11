import Analysis.ThetaAnalytic

/-!
Inversion and translation of theta sums in the CDT v2 Section 11.1 nome.
Mathlib's Jacobi functional equation fixes the principal complex power
and both exponential factors of the normalized second theta.
-/

namespace DirichletL

open Complex Function.Periodic
open scoped Real

private theorem thetaInversion_im_pos {τ : ℂ} (hτ : 0 < τ.im) :
    0 < (-1 / (4 * τ)).im := by
  have h4 : 0 < (4 * τ).im := by
    simpa using mul_pos (by norm_num : (0 : ℝ) < 4) hτ
  simpa only [UpperHalfPlane.coe_mk, inv_neg, neg_div, one_div] using
    (UpperHalfPlane.im_inv_neg_coe_pos ⟨4 * τ, h4⟩)

theorem sum_complexSeries_thetaThreeSeries_inversion {τ : ℂ} (hτ : 0 < τ.im) :
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum (qParam 1 τ) =
      1 / (-I * (2 * τ)) ^ (1 / 2 : ℂ) *
        (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum
          (qParam 1 (-1 / (4 * τ))) := by
  rw [sum_complexSeries_thetaThreeSeries_qParam hτ,
    sum_complexSeries_thetaThreeSeries_qParam (thetaInversion_im_pos hτ)]
  have h0 : τ ≠ 0 := fun h => (ne_of_gt hτ) (congrArg Complex.im h)
  have he : 2 * (-1 / (4 * τ)) = -1 / (2 * τ) := by field_simp; ring
  rw [he]
  simpa only [zero_pow two_ne_zero, mul_zero, zero_div, exp_zero, mul_one,
    ← jacobiTheta_eq_jacobiTheta₂] using jacobiTheta₂_functional_equation 0 (2 * τ)

theorem sum_complexSeries_thetaFourSeries_inversion {τ : ℂ} (hτ : 0 < τ.im) :
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum (qParam 1 τ) =
      1 / (-I * (2 * τ)) ^ (1 / 2 : ℂ) * exp (-π * I / (8 * τ)) *
        (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)).sum
          (qParam 1 (-1 / (4 * τ))) := by
  rw [sum_complexSeries_thetaFourSeries_qParam hτ,
    sum_complexSeries_thetaTwoNormalizedSeries_qParam (thetaInversion_im_pos hτ)]
  have h0 : τ ≠ 0 := fun h => (ne_of_gt hτ) (congrArg Complex.im h)
  have hz : (1 / 2 : ℂ) / (2 * τ) = -(-1 / (4 * τ)) := by field_simp; ring
  have hr : -1 / (2 * τ) = 2 * (-1 / (4 * τ)) := by field_simp; ring
  have he : -π * I * (1 / 2 : ℂ) ^ 2 / (2 * τ) = -π * I / (8 * τ) := by
    ring
  simpa only [hz, hr, he, jacobiTheta₂_neg_left] using
    jacobiTheta₂_functional_equation (1 / 2) (2 * τ)

theorem sum_complexSeries_thetaTwoNormalizedSeries_inversion {τ : ℂ} (hτ : 0 < τ.im) :
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)).sum
      (qParam 1 τ) = 1 / (-I * (2 * τ)) ^ (1 / 2 : ℂ) * exp (-π * I * τ / 2) *
        (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum
          (qParam 1 (-1 / (4 * τ))) := by
  rw [sum_complexSeries_thetaTwoNormalizedSeries_qParam hτ,
    sum_complexSeries_thetaFourSeries_qParam (thetaInversion_im_pos hτ)]
  have h0 : τ ≠ 0 := fun h => (ne_of_gt hτ) (congrArg Complex.im h)
  have hz : τ / (2 * τ) = (1 / 2 : ℂ) := by field_simp
  have hr : -1 / (2 * τ) = 2 * (-1 / (4 * τ)) := by field_simp; ring
  have he : -π * I * τ ^ 2 / (2 * τ) = -π * I * τ / 2 := by
    field_simp
  simpa only [hz, hr, he] using jacobiTheta₂_functional_equation τ (2 * τ)

private theorem qParam_add_half (τ : ℂ) : qParam 1 (τ + 1 / 2) = -qParam 1 τ := by
  simp only [qParam, ofReal_one, div_one]
  have he : 2 * π * I * (τ + 1 / 2) = 2 * π * I * τ + π * I := by ring
  rw [he, exp_add, exp_pi_mul_I, mul_neg_one]

private theorem qParam_add_half_pow_square (τ : ℂ) (n : ℕ) :
    qParam 1 (τ + 1 / 2) ^ (n ^ 2) = (-1 : ℂ) ^ n * qParam 1 τ ^ (n ^ 2) := by
  rw [qParam_add_half, neg_pow, neg_one_pow_congr (Nat.even_pow' two_ne_zero)]

private theorem neg_one_pow_mul_qParam_add_half_pow_square (τ : ℂ) (n : ℕ) :
    (-1 : ℂ) ^ n * qParam 1 (τ + 1 / 2) ^ (n ^ 2) = qParam 1 τ ^ (n ^ 2) := by
  rw [qParam_add_half_pow_square, ← mul_assoc, ← mul_pow]
  simp

private theorem qParam_add_half_pow_pronic (τ : ℂ) (n : ℕ) :
    qParam 1 (τ + 1 / 2) ^ (n * (n + 1)) = qParam 1 τ ^ (n * (n + 1)) := by
  rw [qParam_add_half, (Nat.even_mul_succ_self n).neg_pow]

theorem sum_complexSeries_thetaThreeSeries_add_half {τ : ℂ} (hτ : 0 < τ.im) :
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum
      (qParam 1 (τ + 1 / 2)) =
        (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum
          (qParam 1 τ) := by
  have ht : 0 < (τ + (1 / 2 : ℂ)).im := by simpa using hτ
  rw [sum_complexSeries_thetaThreeSeries_qParam ht, sum_complexSeries_thetaFourSeries_qParam hτ]
  have hs := hasSum_qParam_square ht
  simp only [qParam_add_half_pow_square] at hs
  have he := congrArg (fun z : ℂ => 2 * z - 1)
    (hs.unique (hasSum_neg_one_pow_mul_qParam_square hτ))
  convert he using 1 <;> ring

theorem sum_complexSeries_thetaFourSeries_add_half {τ : ℂ} (hτ : 0 < τ.im) :
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum
      (qParam 1 (τ + 1 / 2)) =
        (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum
          (qParam 1 τ) := by
  have ht : 0 < (τ + (1 / 2 : ℂ)).im := by simpa using hτ
  rw [sum_complexSeries_thetaFourSeries_qParam ht, sum_complexSeries_thetaThreeSeries_qParam hτ]
  have hs := hasSum_neg_one_pow_mul_qParam_square ht
  simp only [neg_one_pow_mul_qParam_add_half_pow_square] at hs
  have he := congrArg (fun z : ℂ => 2 * z - 1) (hs.unique (hasSum_qParam_square hτ))
  convert he using 1 <;> ring

theorem sum_complexSeries_thetaTwoNormalizedSeries_add_half {τ : ℂ} (hτ : 0 < τ.im) :
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)).sum
      (qParam 1 (τ + 1 / 2)) =
        (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)).sum
          (qParam 1 τ) := by
  have ht : 0 < (τ + (1 / 2 : ℂ)).im := by simpa using hτ
  rw [sum_complexSeries_thetaTwoNormalizedSeries_qParam ht,
    sum_complexSeries_thetaTwoNormalizedSeries_qParam hτ]
  have hs := hasSum_qParam_pronic ht
  simp only [qParam_add_half_pow_pronic] at hs
  have he := congrArg (fun z : ℂ => 2 * z) (hs.unique (hasSum_qParam_pronic hτ))
  convert he using 1 <;> ring

end DirichletL

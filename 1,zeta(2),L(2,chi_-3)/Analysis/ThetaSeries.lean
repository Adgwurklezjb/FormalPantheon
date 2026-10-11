import Analysis.SparsePowerSeries

/-!
Integer formal theta series for the lattice theta in CDT v2 Section 11.1.
The normalized second theta has the fractional prefactor removed; its
-/

namespace DirichletL

/-- The nonnegative square exponents, with their canonical indexing. -/
def natSquareEmbedding : ℕ ↪ ℕ where
  toFun n := n ^ 2
  inj' := (Nat.pow_left_strictMono two_ne_zero).injective

/-- The exponents remaining after the half-integer theta prefactor is removed. -/
def natPronicEmbedding : ℕ ↪ ℕ where
  toFun n := n * (n + 1)
  inj' := by
    have h : StrictMono (fun n : ℕ => n * (n + 1)) :=
      strictMono_nat_of_lt_succ (fun n => by nlinarith)
    exact h.injective

@[simp] theorem natSquareEmbedding_apply (n : ℕ) : natSquareEmbedding n = n ^ 2 := rfl

@[simp] theorem natPronicEmbedding_apply (n : ℕ) : natPronicEmbedding n = n * (n + 1) := rfl

/-- The integer-square theta series, with the zero exponent counted once. -/
noncomputable def thetaThreeSeries : PowerSeries ℤ :=
  2 * sparsePowerSeries natSquareEmbedding (fun _ => 1) - 1

/-- The alternating integer-square theta series. -/
noncomputable def thetaFourSeries : PowerSeries ℤ :=
  2 * sparsePowerSeries natSquareEmbedding (fun n => (-1) ^ n) - 1

/-- The half-integer theta series after removing its fractional prefactor. -/
noncomputable def thetaTwoNormalizedSeries : PowerSeries ℤ :=
  2 * sparsePowerSeries natPronicEmbedding (fun _ => 1)

open scoped PowerSeries.WithPiTopology

theorem hasSum_X_pow_square :
    HasSum (fun n : ℕ => (PowerSeries.X : PowerSeries ℤ) ^ (n ^ 2))
      (sparsePowerSeries natSquareEmbedding (fun _ => 1)) := by
  simpa using hasSum_sparsePowerSeries natSquareEmbedding (fun _ => (1 : ℤ))

theorem hasSum_neg_one_pow_mul_X_square :
    HasSum (fun n : ℕ => (-1 : PowerSeries ℤ) ^ n * PowerSeries.X ^ (n ^ 2))
      (sparsePowerSeries natSquareEmbedding (fun n => (-1) ^ n)) := by
  simpa using hasSum_sparsePowerSeries natSquareEmbedding (fun n => (-1 : ℤ) ^ n)

theorem hasSum_X_pow_pronic :
    HasSum (fun n : ℕ => (PowerSeries.X : PowerSeries ℤ) ^ (n * (n + 1)))
      (sparsePowerSeries natPronicEmbedding (fun _ => 1)) := by
  simpa using hasSum_sparsePowerSeries natPronicEmbedding (fun _ => (1 : ℤ))

@[simp] theorem constantCoeff_thetaThreeSeries :
    PowerSeries.constantCoeff (R := ℤ) thetaThreeSeries = 1 := by
  have h := coeff_sparsePowerSeries_apply natSquareEmbedding (fun _ => (1 : ℤ)) 0
  simp only [natSquareEmbedding_apply, zero_pow two_ne_zero,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  norm_num [thetaThreeSeries, h, map_ofNat]

@[simp] theorem constantCoeff_thetaFourSeries :
    PowerSeries.constantCoeff (R := ℤ) thetaFourSeries = 1 := by
  have h := coeff_sparsePowerSeries_apply natSquareEmbedding (fun n => (-1 : ℤ) ^ n) 0
  simp only [natSquareEmbedding_apply, zero_pow two_ne_zero, pow_zero,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  norm_num [thetaFourSeries, h, map_ofNat]

@[simp] theorem constantCoeff_thetaTwoNormalizedSeries :
    PowerSeries.constantCoeff (R := ℤ) thetaTwoNormalizedSeries = 2 := by
  have h := coeff_sparsePowerSeries_apply natPronicEmbedding (fun _ => (1 : ℤ)) 0
  simp only [natPronicEmbedding_apply, zero_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  norm_num [thetaTwoNormalizedSeries, h, map_ofNat]

end DirichletL

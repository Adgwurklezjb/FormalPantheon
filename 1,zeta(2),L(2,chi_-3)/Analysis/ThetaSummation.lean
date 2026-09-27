import Analysis.ThetaSeries

/-!
Scalar theta sums in the CDT v2 Section 11.1 convention q=exp(2*pi*i*tau).
The canonical Mathlib theta functions have second argument 2*tau.
-/

namespace DirichletL

open Complex Function.Periodic
open scoped Real

private theorem qParam_one_pow (τ : ℂ) (n : ℕ) :
    qParam 1 τ ^ n = exp ((n : ℂ) * (2 * π * I * τ)) := by
  simp only [qParam, ofReal_one, div_one, exp_nat_mul]

private theorem im_two_mul_pos {τ : ℂ} (hτ : 0 < τ.im) : 0 < (2 * τ).im := by
  simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hτ

private theorem jacobiTheta_square_term (τ : ℂ) (n : ℕ) :
    exp (π * I * ((n : ℂ) + 1) ^ 2 * (2 * τ)) = qParam 1 τ ^ ((n + 1) ^ 2) := by
  rw [qParam_one_pow]
  apply congrArg exp
  push_cast
  ring

theorem hasSum_qParam_square {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => qParam 1 τ ^ (n ^ 2)) ((jacobiTheta (2 * τ) + 1) / 2) := by
  have h := hasSum_nat_jacobiTheta (im_two_mul_pos hτ)
  simp only [jacobiTheta_square_term] at h
  have hfull := (hasSum_nat_add_iff (f := fun n : ℕ => qParam 1 τ ^ (n ^ 2)) 1).mp h
  have he : (jacobiTheta (2 * τ) - 1) / 2 + 1 = (jacobiTheta (2 * τ) + 1) / 2 := by ring
  simpa only [Finset.sum_range_one, zero_pow two_ne_zero, pow_zero, he] using hfull

private theorem jacobiTheta_four_term_nat (τ : ℂ) (n : ℕ) :
    jacobiTheta₂_term n (1 / 2) (2 * τ) = (-1) ^ n * qParam 1 τ ^ (n ^ 2) := by
  rw [jacobiTheta₂_term, qParam_one_pow, ← exp_pi_mul_I, ← exp_nat_mul, ← exp_add]
  apply congrArg exp
  push_cast
  ring

private theorem jacobiTheta_four_term_neg_nat (τ : ℂ) (n : ℕ) :
    jacobiTheta₂_term (-(n : ℤ)) (1 / 2) (2 * τ) = (-1) ^ n * qParam 1 τ ^ (n ^ 2) := by
  have he : exp (-(π * I)) = (-1 : ℂ) := by simp [exp_neg, exp_pi_mul_I]
  rw [jacobiTheta₂_term, qParam_one_pow, ← he, ← exp_nat_mul, ← exp_add]
  apply congrArg exp
  push_cast
  ring

theorem hasSum_neg_one_pow_mul_qParam_square {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ n * qParam 1 τ ^ (n ^ 2))
      ((jacobiTheta₂ (1 / 2) (2 * τ) + 1) / 2) := by
  have h := (hasSum_jacobiTheta₂_term (1 / 2) (im_two_mul_pos hτ)).nat_add_neg
  have hz : jacobiTheta₂_term 0 (1 / 2) (2 * τ) = 1 := by simp [jacobiTheta₂_term]
  rw [hz] at h
  simp only [jacobiTheta_four_term_nat, jacobiTheta_four_term_neg_nat] at h
  simpa only [add_self_div_two] using h.div_const (2 : ℂ)

private theorem jacobiTheta_pronic_term_nat (τ : ℂ) (n : ℕ) :
    jacobiTheta₂_term n τ (2 * τ) = qParam 1 τ ^ (n * (n + 1)) := by
  rw [jacobiTheta₂_term, qParam_one_pow]
  apply congrArg exp
  push_cast
  ring

private theorem jacobiTheta_pronic_term_neg_succ (τ : ℂ) (n : ℕ) :
    jacobiTheta₂_term (-(n + 1 : ℤ)) τ (2 * τ) = qParam 1 τ ^ (n * (n + 1)) := by
  rw [jacobiTheta₂_term, qParam_one_pow]
  apply congrArg exp
  push_cast
  ring

theorem hasSum_qParam_pronic {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => qParam 1 τ ^ (n * (n + 1))) (jacobiTheta₂ τ (2 * τ) / 2) := by
  have h := (hasSum_jacobiTheta₂_term τ (im_two_mul_pos hτ)).nat_add_neg_add_one
  simp only [jacobiTheta_pronic_term_nat, jacobiTheta_pronic_term_neg_succ] at h
  simpa only [add_self_div_two] using h.div_const (2 : ℂ)

end DirichletL

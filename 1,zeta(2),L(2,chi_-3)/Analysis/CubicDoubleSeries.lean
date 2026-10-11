import Mathlib

/-!
Absolute convergence for the differentiated beta/gamma numerator double
series of CDT v2, Section 11.1. The positive-index and zero-radius checks
-/

namespace DirichletL

theorem summable_norm_cubicDoubleSeries_of_bounded (a : ℕ → ℕ → ℂ) {M : ℝ}
    (hM : 0 ≤ M) (ha : ∀ c r, ‖a c r‖ ≤ M) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun p : ℕ × ℕ =>
      ‖a (p.1 + 1) (p.2 + 1) * ((p.2 + 1 : ℕ) : ℂ) ^ 2 *
        q ^ ((p.1 + 1) * (p.2 + 1))‖) := by
  have hc : Summable (fun c : ℕ => ‖q‖ ^ c) :=
    summable_geometric_of_lt_one (norm_nonneg _) hq
  have hr : Summable (fun r : ℕ => ((r + 1 : ℕ) : ℝ) ^ 2 * ‖q‖ ^ (r + 1)) :=
    (summable_nat_add_iff 1).2
      (summable_pow_mul_geometric_of_norm_lt_one 2 (by simpa using hq))
  have hprod := (hc.mul_of_nonneg hr (fun _ => by positivity) (fun _ => by positivity)).mul_left M
  refine hprod.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  rintro ⟨m, n⟩
  have hp : ‖q‖ ^ ((m + 1) * (n + 1)) ≤ ‖q‖ ^ (m + (n + 1)) :=
    pow_le_pow_of_le_one (norm_nonneg _) hq.le (by nlinarith)
  calc
    ‖a (m + 1) (n + 1) * ((n + 1 : ℕ) : ℂ) ^ 2 * q ^ ((m + 1) * (n + 1))‖
      = ‖a (m + 1) (n + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ 2 *
          ‖q‖ ^ ((m + 1) * (n + 1)) := by simp only [norm_mul, norm_pow, Complex.norm_natCast]
    _ ≤ M * ((n + 1 : ℕ) : ℝ) ^ 2 * ‖q‖ ^ (m + (n + 1)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (ha _ _) (sq_nonneg _)) hp
        (by positivity) (by positivity)
    _ = M * (‖q‖ ^ m * (((n + 1 : ℕ) : ℝ) ^ 2 * ‖q‖ ^ (n + 1))) := by
      rw [pow_add]
      ring

theorem summable_cubicDoubleSeries_of_bounded (a : ℕ → ℕ → ℂ) {M : ℝ}
    (hM : 0 ≤ M) (ha : ∀ c r, ‖a c r‖ ≤ M) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun p : ℕ × ℕ =>
      a (p.1 + 1) (p.2 + 1) * ((p.2 + 1 : ℕ) : ℂ) ^ 2 *
        q ^ ((p.1 + 1) * (p.2 + 1))) :=
  (summable_norm_cubicDoubleSeries_of_bounded a hM ha hq).of_norm

end DirichletL

import Mathlib

/-!
Exact power errors for the finite profile in CDT v2's contour estimate, TeX 8384-8404.
Meanings and recurrence checks precede these bodies in
-/

namespace DirichletL

theorem norm_pow_sub_pow_le_of_norm_le (n : ℕ) {z w : ℂ} {ρ : ℝ}
    (hz : ‖z‖ ≤ ρ) (hw : ‖w‖ ≤ ρ) :
    ‖z ^ n - w ^ n‖ ≤ (n : ℝ) * ρ ^ (n - 1) * ‖z - w‖ := by
  have hρ : 0 ≤ ρ := (norm_nonneg z).trans hz
  have hb (k : ℕ) : ‖z ^ (k + 1) - w ^ (k + 1)‖ ≤
      ((k + 1 : ℕ) : ℝ) * ρ ^ k * ‖z - w‖ := by
    induction k with
    | zero => simp
    | succ k ih =>
      have heq : z ^ (k + 1 + 1) - w ^ (k + 1 + 1) =
          z * (z ^ (k + 1) - w ^ (k + 1)) + (z - w) * w ^ (k + 1) := by
        simp only [pow_succ]
        ring
      rw [heq]
      calc
        _ ≤ ‖z * (z ^ (k + 1) - w ^ (k + 1))‖ + ‖(z - w) * w ^ (k + 1)‖ :=
          norm_add_le _ _
        _ = ‖z‖ * ‖z ^ (k + 1) - w ^ (k + 1)‖ + ‖z - w‖ * ‖w‖ ^ (k + 1) := by
          rw [norm_mul, norm_mul, norm_pow]
        _ ≤ ρ * (((k + 1 : ℕ) : ℝ) * ρ ^ k * ‖z - w‖) +
            ‖z - w‖ * ρ ^ (k + 1) := by gcongr
        _ = _ := by simp only [pow_succ, Nat.cast_add, Nat.cast_one]; ring
  cases n with
  | zero => simp
  | succ n => simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hb n

theorem norm_pow_sub_pow_sub_linear_le (n : ℕ) {z w : ℂ} {ρ : ℝ}
    (hz : ‖z‖ ≤ ρ) (hw : ‖w‖ ≤ ρ) :
    ‖z ^ n - w ^ n - (n : ℂ) * w ^ (n - 1) * (z - w)‖ ≤
      ((n : ℝ) * ((n - 1 : ℕ) : ℝ) / 2) * ρ ^ (n - 2) * ‖z - w‖ ^ 2 := by
  have hρ : 0 ≤ ρ := (norm_nonneg z).trans hz
  have hb (k : ℕ) :
      ‖z ^ (k + 2) - w ^ (k + 2) - ((k + 2 : ℕ) : ℂ) * w ^ (k + 1) * (z - w)‖ ≤
        (((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) / 2) * ρ ^ k * ‖z - w‖ ^ 2 := by
    induction k with
    | zero =>
      have heq : z ^ 2 - w ^ 2 - (2 : ℂ) * w * (z - w) = (z - w) ^ 2 := by ring
      norm_num [heq, norm_pow]
    | succ k ih =>
      have heq :
          z ^ (k + 1 + 2) - w ^ (k + 1 + 2) -
              ((k + 1 + 2 : ℕ) : ℂ) * w ^ (k + 1 + 1) * (z - w) =
            z * (z ^ (k + 2) - w ^ (k + 2) -
              ((k + 2 : ℕ) : ℂ) * w ^ (k + 1) * (z - w)) +
            ((k + 2 : ℕ) : ℂ) * w ^ (k + 1) * (z - w) ^ 2 := by
        simp only [pow_succ, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
        ring
      rw [heq]
      calc
        _ ≤ ‖z * (z ^ (k + 2) - w ^ (k + 2) -
              ((k + 2 : ℕ) : ℂ) * w ^ (k + 1) * (z - w))‖ +
            ‖((k + 2 : ℕ) : ℂ) * w ^ (k + 1) * (z - w) ^ 2‖ := norm_add_le _ _
        _ = ‖z‖ * ‖z ^ (k + 2) - w ^ (k + 2) -
              ((k + 2 : ℕ) : ℂ) * w ^ (k + 1) * (z - w)‖ +
            ((k + 2 : ℕ) : ℝ) * ‖w‖ ^ (k + 1) * ‖z - w‖ ^ 2 := by
          simp only [norm_mul, norm_pow, Complex.norm_natCast]
        _ ≤ ρ * ((((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) / 2) *
              ρ ^ k * ‖z - w‖ ^ 2) +
            ((k + 2 : ℕ) : ℝ) * ρ ^ (k + 1) * ‖z - w‖ ^ 2 := by gcongr
        _ = _ := by simp only [pow_succ, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]; ring
  rcases n with _ | n
  · simp
  rcases n with _ | n
  · simp
  simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hb n

end DirichletL

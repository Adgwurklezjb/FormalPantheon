import Mathlib

/-!
Exact logarithmic tails for CDT v2's signed contour profile, TeX 6947-6948 and 8384-8404.
-/

namespace DirichletL

/-- The first odd terms of the real logarithmic difference series. -/
noncomputable def logOddPartial (N : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * u ^ (2 * k + 1)

theorem abs_log_sub_log_sub_logOddPartial_le (N : ℕ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    |Real.log (1 + u) - Real.log (1 - u) - logOddPartial N u| ≤
      2 * u ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - u ^ 2)) := by
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one (by rwa [abs_of_nonneg hu0])
  have hsplit := hs.summable.sum_add_tsum_nat_add N
  rw [hs.tsum_eq] at hsplit
  have heq : Real.log (1 + u) - Real.log (1 - u) - logOddPartial N u =
      ∑' j : ℕ, (2 : ℝ) * (1 / (2 * ((j + N : ℕ) : ℝ) + 1)) *
        u ^ (2 * (j + N) + 1) := by
    dsimp only [logOddPartial]
    linear_combination -hsplit
  rw [heq, ← Real.norm_eq_abs]
  have hu2 : u ^ 2 < 1 := pow_lt_one₀ hu0 hu1 (by norm_num)
  have hgeom : HasSum (fun j : ℕ =>
      (2 * u ^ (2 * N + 1) / (2 * (N : ℝ) + 1)) * (u ^ 2) ^ j)
      (2 * u ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - u ^ 2))) := by
    convert (hasSum_geometric_of_lt_one (sq_nonneg u) hu2).mul_left
      (2 * u ^ (2 * N + 1) / (2 * (N : ℝ) + 1)) using 1
    simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc]
    ring
  apply tsum_of_norm_bounded hgeom
  intro j
  have hodd : (2 * (N : ℝ) + 1) ≤ 2 * ((j + N : ℕ) : ℝ) + 1 := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) j]
  calc
    _ = (2 / (2 * ((j + N : ℕ) : ℝ) + 1)) * u ^ (2 * (j + N) + 1) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      ring
    _ ≤ (2 / (2 * (N : ℝ) + 1)) * u ^ (2 * (j + N) + 1) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num)
        (by positivity) hodd) (pow_nonneg hu0 _)
    _ = _ := by
      rw [show 2 * (j + N) + 1 = (2 * N + 1) + 2 * j by omega, pow_add, pow_mul]
      ring

theorem abs_log_sub_logOddPartial_fourteen_le {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    |Real.log x - logOddPartial 14 ((x - 1) / (x + 1))| ≤ 1 / (116 * 3 ^ 27) := by
  let u := (x - 1) / (x + 1)
  have hxp : 0 < x + 1 := by linarith
  have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr hx1) hxp.le
  have hu : u ≤ 1 / 3 := (div_le_iff₀ hxp).2 (by linarith)
  have hu1 : u < 1 := by linarith
  have heq : Real.log x = Real.log (1 + u) - Real.log (1 - u) := by
    have hp : 0 < 1 + u := by linarith
    have hm : 0 < 1 - u := by linarith
    rw [← Real.log_div hp.ne' hm.ne']
    congr 1
    apply (eq_div_iff hm.ne').2
    dsimp only [u]
    field_simp [hxp.ne']
    ring
  rw [heq]
  apply (abs_log_sub_log_sub_logOddPartial_le 14 hu0 hu1).trans
  calc
    _ ≤ 2 * (1 / 3 : ℝ) ^ (2 * 14 + 1) /
        ((2 * (14 : ℝ) + 1) * (1 - (1 / 3 : ℝ) ^ 2)) := by gcongr <;> norm_num
    _ = _ := by norm_num

end DirichletL

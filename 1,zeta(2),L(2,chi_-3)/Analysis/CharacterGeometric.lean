import Foundations.ChiMinusThree

/-!
The geometric generating function of the real character modulo 3.  This is
the elementary kernel for the dilogarithmic C-series of CDT v2 Section 11.1,
source lines 7674-7680.
-/

namespace DirichletL

theorem summable_chiMinusThree_mul_pow {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => chiMinusThree n * q ^ n) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => q ^ n)
    (summable_geometric_of_lt_one hq hq1)
  intro n
  rw [norm_mul, norm_pow, Real.norm_of_nonneg hq]
  simpa using mul_le_mul_of_nonneg_right (norm_chiMinusThree_le_one n)
    (pow_nonneg hq n)

/-- The character series sums to a rational kernel on `0 ≤ q < 1`. -/
theorem hasSum_chiMinusThree_mul_pow {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => chiMinusThree n * q ^ n) (q / (1 + q + q ^ 2)) := by
  let f : ℕ → ℝ := fun n => chiMinusThree n * q ^ n
  have hs : Summable (fun p : ℕ × Fin 3 => f ((Nat.divModEquiv 3).symm p)) :=
    ((Nat.divModEquiv 3).symm.summable_iff (f := f)).mpr
      (summable_chiMinusThree_mul_pow hq hq1)
  have hq3 : q ^ 3 < 1 := pow_lt_one₀ hq hq1 (by decide : 3 ≠ 0)
  have hg := hasSum_geometric_of_lt_one (pow_nonneg hq 3) hq3
  have hres : HasSum (fun k : ℕ => q ^ (3 * k + 1) - q ^ (3 * k + 2))
      ((1 - q ^ 3)⁻¹ * q - (1 - q ^ 3)⁻¹ * q ^ 2) := by
    simpa only [pow_add, pow_mul, pow_one] using
      (hg.mul_right q).sub (hg.mul_right (q ^ 2))
  have hsum : (∑' n : ℕ, f n) = q / (1 + q + q ^ 2) := by
    calc
      (∑' n : ℕ, f n) = ∑' p : ℕ × Fin 3, f ((Nat.divModEquiv 3).symm p) :=
        ((Nat.divModEquiv 3).symm.tsum_eq f).symm
      _ = ∑' k : ℕ, ∑' i : Fin 3, f ((Nat.divModEquiv 3).symm (k, i)) :=
        hs.tsum_prod
      _ = ∑' k : ℕ, (q ^ (3 * k + 1) - q ^ (3 * k + 2)) := by
        apply tsum_congr
        intro k
        simp [tsum_fintype, Fin.sum_univ_succ, Nat.divModEquiv, f, chiMinusThree,
          Nat.add_mod, Nat.mul_mod, Nat.mul_comm, sub_eq_add_neg, one_add_one_eq_two]
      _ = (1 - q ^ 3)⁻¹ * q - (1 - q ^ 3)⁻¹ * q ^ 2 := hres.tsum_eq
      _ = q / (1 + q + q ^ 2) := by
        have hden : 1 + q + q ^ 2 ≠ 0 := by positivity
        have hgeom : 1 - q ^ 3 ≠ 0 := by linarith
        field_simp
        ring
  exact hsum ▸ (summable_chiMinusThree_mul_pow hq hq1).hasSum

theorem tsum_chiMinusThree_mul_pow {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    (∑' n : ℕ, chiMinusThree n * q ^ n) = q / (1 + q + q ^ 2) :=
  (hasSum_chiMinusThree_mul_pow hq hq1).tsum_eq

end DirichletL

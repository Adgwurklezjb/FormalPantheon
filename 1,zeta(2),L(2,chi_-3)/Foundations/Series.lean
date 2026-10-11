import Foundations.ChiMinusThree

/-!
Convergence and normalization facts for the two real series.
-/

namespace DirichletL

theorem summable_zetaTwo_terms :
    Summable (fun n : ℕ => if n = 0 then 0 else 1 / (n : ℝ) ^ 2) := by
  apply hasSum_zeta_two.summable.congr
  intro n
  by_cases hn : n = 0 <;> simp [hn]

theorem zetaTwo_eq_tsum :
    zetaTwo = ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
  unfold zetaTwo
  apply tsum_congr
  intro n
  by_cases hn : n = 0 <;> simp [hn]

theorem summable_lTwoChiMinusThree_terms :
    Summable (fun n : ℕ => chiMinusThree n / (n : ℝ) ^ 2) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => 1 / (n : ℝ) ^ 2)
    ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
  intro n
  rw [norm_div, norm_pow, Real.norm_natCast]
  exact div_le_div_of_nonneg_right (norm_chiMinusThree_le_one n) (sq_nonneg _)

theorem lTwoChiMinusThree_eq_tsum :
    lTwoChiMinusThree = ∑' n : ℕ, chiMinusThree n / (n : ℝ) ^ 2 :=
  rfl

/-- Convergence to the real L-value in CDT v2, Theorem A. -/
theorem hasSum_lTwoChiMinusThree :
    HasSum (fun n : ℕ => chiMinusThree n / (n : ℝ) ^ 2) lTwoChiMinusThree :=
  summable_lTwoChiMinusThree_terms.hasSum

/-- The residue-class expression displayed in CDT v2, Theorem A. -/
theorem lTwoChiMinusThree_eq_residue_tsum :
    lTwoChiMinusThree = ∑' k : ℕ,
      (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2) := by
  let f : ℕ → ℝ := fun n => chiMinusThree n / (n : ℝ) ^ 2
  have hs : Summable (fun p : ℕ × Fin 3 => f ((Nat.divModEquiv 3).symm p)) :=
    ((Nat.divModEquiv 3).symm.summable_iff (f := f)).mpr
      summable_lTwoChiMinusThree_terms
  calc
    lTwoChiMinusThree = ∑' p : ℕ × Fin 3, f ((Nat.divModEquiv 3).symm p) :=
      ((Nat.divModEquiv 3).symm.tsum_eq f).symm
    _ = ∑' k : ℕ, ∑' i : Fin 3, f ((Nat.divModEquiv 3).symm (k, i)) :=
      hs.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro k
      simp [tsum_fintype, Fin.sum_univ_succ, Nat.divModEquiv, f, chiMinusThree,
        Nat.add_mod, Nat.mul_mod, Nat.mul_comm, sub_eq_add_neg, neg_div, one_add_one_eq_two]

/-- The residue-class series for `L(2, chi_-3)` is strictly positive. -/
theorem lTwoChiMinusThree_pos : 0 < lTwoChiMinusThree := by
  let f : ℕ → ℝ := fun n => chiMinusThree n / (n : ℝ) ^ 2
  let g : ℕ → ℝ := fun k =>
    1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2
  have hf : Summable f := by
    simpa [f] using summable_lTwoChiMinusThree_terms
  have hi₁ : Function.Injective (fun k : ℕ => 3 * k + 1) := by
    intro k l h
    change 3 * k + 1 = 3 * l + 1 at h
    omega
  have hi₂ : Function.Injective (fun k : ℕ => 3 * k + 2) := by
    intro k l h
    change 3 * k + 2 = 3 * l + 2 at h
    omega
  have hg : Summable g := by
    exact (hf.comp_injective hi₁).add (hf.comp_injective hi₂) |>.congr
      (fun k => by
        simp [f, g, Function.comp_def, chiMinusThree, div_eq_mul_inv]
        ring)
  have hnonneg : ∀ k : ℕ, 0 ≤ g k := by
    intro k
    dsimp [g]
    have h₁N : 0 < 3 * k + 1 := by omega
    have h₁ : (0 : ℝ) < ((3 * k + 1 : ℕ) : ℝ) := by exact_mod_cast h₁N
    have hlt : (3 * k + 1 : ℕ) < (3 * k + 2 : ℕ) := by omega
    have hltR : ((3 * k + 1 : ℕ) : ℝ) < ((3 * k + 2 : ℕ) : ℝ) := by
      exact_mod_cast hlt
    have hsq : ((3 * k + 1 : ℕ) : ℝ) ^ 2 <
        ((3 * k + 2 : ℕ) : ℝ) ^ 2 := by
      nlinarith
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [hsq]
  have hzero : 0 < g 0 := by
    norm_num [g]
  rw [lTwoChiMinusThree_eq_residue_tsum]
  exact hg.tsum_pos hnonneg 0 hzero

end DirichletL

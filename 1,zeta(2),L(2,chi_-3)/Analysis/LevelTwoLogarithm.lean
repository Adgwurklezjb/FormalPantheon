import Analysis.LevelTwoHauptmodul

/-!
The logarithm of CDT v2's level-two product, equation `defofh`, TeX 6947-6948.
-/

namespace DirichletL

/-- The sum of principal logarithms of the level-two product's factors, indexed from one. -/
noncomputable def levelTwoLogSeries (q : ℂ) : ℂ :=
  ∑' n : ℕ, Complex.log (1 + q ^ (n + 1))

theorem summable_levelTwoLogSeries {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => Complex.log (1 + q ^ (n + 1))) := by
  apply Complex.summable_log_one_add_of_summable
  simpa only [pow_succ] using (summable_geometric_of_norm_lt_one hq).mul_right q

theorem exp_levelTwoLogSeries_eq_product {q : ℂ} (hq : ‖q‖ < 1) :
    Complex.exp (levelTwoLogSeries q) = ∏' n : ℕ, (1 + q ^ (n + 1)) := by
  apply Complex.cexp_tsum_eq_tprod _ (summable_levelTwoLogSeries hq)
  intro n
  apply Complex.slitPlane_ne_zero
  apply Complex.mem_slitPlane_of_norm_lt_one
  rw [norm_pow]
  calc
    ‖q‖ ^ (n + 1) ≤ ‖q‖ := by
      simpa only [pow_one] using pow_le_pow_of_le_one (norm_nonneg q) hq.le
        (show 1 ≤ n + 1 by omega)
    _ < 1 := hq

theorem log_norm_levelTwoHauptmodul {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    Real.log ‖levelTwoHauptmodul q‖ =
      8 * Real.log 2 + Real.log ‖q‖ + 24 * (levelTwoLogSeries q).re := by
  let T : ℂ := ∏' n : ℕ, (1 + q ^ (n + 1))
  have hT : T ≠ 0 := by
    simpa only [T, one_mul] using tprod_one_add_mul_pow_ne_zero
      (s := (1 : ℂ)) (e := fun n => n + 1) (by simp) (fun _ => le_rfl) hq
  have hlogT : Real.log ‖T‖ = (levelTwoLogSeries q).re := by
    change Real.log ‖∏' n : ℕ, (1 + q ^ (n + 1))‖ = _
    rw [← exp_levelTwoLogSeries_eq_product hq, Complex.norm_exp, Real.log_exp]
  have h256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 8
    norm_num at h
    exact h
  have hnorm : ‖levelTwoHauptmodul q‖ = 256 * ‖q‖ * ‖T‖ ^ 24 := by
    norm_num [levelTwoHauptmodul, T, norm_mul, norm_pow]
  rw [hnorm, Real.log_mul (mul_ne_zero (by norm_num) (norm_ne_zero_iff.mpr hq0))
    (pow_ne_zero _ (norm_ne_zero_iff.mpr hT)),
    Real.log_mul (by norm_num) (norm_ne_zero_iff.mpr hq0), Real.log_pow, hlogT, h256,
    Nat.cast_ofNat]

end DirichletL

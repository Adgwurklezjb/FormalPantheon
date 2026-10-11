import Analysis.LevelTwoHauptmodul

/-!
The positive real preimage used at the start of CDT author Lemma A.4.4,
page 205, from the level-two product recalled on page 204.
Meanings and endpoint checks precede the bodies in
-/

namespace DirichletL

theorem levelTwoHauptmodul_ofReal {q : ℝ} (hq : |q| < 1) :
    levelTwoHauptmodul (q : ℂ) =
      ((-256 * q * (∏' n : ℕ, (1 + q ^ (n + 1))) ^ 24 : ℝ) : ℂ) := by
  have hp : Multipliable (fun n : ℕ => (1 + q ^ (n + 1) : ℝ)) := by
    apply Real.multipliable_one_add_of_summable
    simpa only [pow_succ] using (summable_geometric_of_abs_lt_one hq).mul_right q
  have hm := hp.map_tprod Complex.ofRealHom Complex.continuous_ofReal
  simp only [Complex.ofRealHom_eq_coe, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_pow] at hm
  rw [levelTwoHauptmodul, ← hm]
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.ofReal_pow]

theorem levelTwoHauptmodul_ofReal_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    (levelTwoHauptmodul (q : ℂ)).re ≤ -256 * q := by
  have hqa : |q| < 1 := by simpa only [abs_of_nonneg hq] using hq1
  have hp : Multipliable (fun n : ℕ => (1 + q ^ (n + 1) : ℝ)) := by
    apply Real.multipliable_one_add_of_summable
    simpa only [pow_succ] using (summable_geometric_of_abs_lt_one hqa).mul_right q
  have hP : (1 : ℝ) ≤ ∏' n : ℕ, (1 + q ^ (n + 1)) := by
    apply le_hasProd_of_le_prod hp.hasProd
    intro s
    simpa only [Finset.prod_const_one] using
      (Finset.prod_le_prod (s := s) (f := fun _ => (1 : ℝ))
        (g := fun n => 1 + q ^ (n + 1)) (fun _ _ => zero_le_one)
        (fun n _ => le_add_of_nonneg_right (pow_nonneg hq (n + 1))))
  rw [levelTwoHauptmodul_ofReal hqa, Complex.ofReal_re]
  have hneg : -256 * q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by norm_num) hq
  simpa only [mul_one] using
    (mul_le_mul_of_nonpos_left (one_le_pow₀ hP (n := 24)) hneg)

theorem exists_levelTwoHauptmodul_eq_neg_one_div_seventyTwo :
    ∃ q : ℝ, q ∈ Set.Ioo 0 (1 / 10000) ∧
      levelTwoHauptmodul (q : ℂ) = -1 / 72 := by
  let f (q : ℝ) : ℝ := (levelTwoHauptmodul (q : ℂ)).re
  have hmaps : Set.MapsTo (fun q : ℝ => (q : ℂ))
      (Set.Icc 0 (1 / 10000)) (Metric.ball 0 1) := by
    intro q hq
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hq.1] using (lt_of_le_of_lt hq.2 (by norm_num : (1 / 10000 : ℝ) < 1))
  have hf : ContinuousOn f (Set.Icc 0 (1 / 10000)) :=
    Complex.continuous_re.comp_continuousOn
      (analyticOnNhd_levelTwoHauptmodul.continuousOn.comp
        Complex.continuous_ofReal.continuousOn hmaps)
  have hzero : f 0 = 0 := by simp [f, levelTwoHauptmodul_zero]
  have hend : f (1 / 10000) ≤ -256 * (1 / 10000) :=
    levelTwoHauptmodul_ofReal_le (by norm_num) (by norm_num)
  have htarget : -(1 / 72 : ℝ) ∈ Set.Ioo (f (1 / 10000)) (f 0) := by
    constructor
    · exact lt_of_le_of_lt hend (by norm_num)
    · rw [hzero]
      norm_num
  obtain ⟨q, hq, hv⟩ := intermediate_value_Ioo' (by norm_num : (0 : ℝ) ≤ 1 / 10000)
    hf htarget
  have hqa : |q| < 1 := by
    rw [abs_of_pos hq.1]
    exact hq.2.trans (by norm_num)
  have hreal : -256 * q * (∏' n : ℕ, (1 + q ^ (n + 1))) ^ 24 = -(1 / 72 : ℝ) := by
    simpa only [f, levelTwoHauptmodul_ofReal hqa, Complex.ofReal_re] using hv
  refine ⟨q, hq, ?_⟩
  rw [levelTwoHauptmodul_ofReal hqa, hreal]
  norm_num

end DirichletL

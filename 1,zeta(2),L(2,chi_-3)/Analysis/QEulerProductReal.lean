import Analysis.QEulerProduct

/-!
The real Euler products used in CDT v2, Section 11.1, equation `haupt`.
Positivity follows from Mathlib's convergent logarithm sum, and the
complex identity maps the actual convergent real product. See
-/

namespace DirichletL

theorem multipliable_real_qEulerProduct_factors {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Multipliable (fun n : ℕ => 1 - q ^ (n + 1)) := by
  have hs : Summable (fun n : ℕ => -(q ^ (n + 1))) := by
    simpa only [pow_succ] using ((summable_geometric_of_lt_one hq0 hq1).mul_right q).neg
  simpa only [sub_eq_add_neg] using Real.multipliable_one_add_of_summable hs

theorem qEulerProduct_ofReal {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    qEulerProduct (q : ℂ) = ((∏' n : ℕ, (1 - q ^ (n + 1)) : ℝ) : ℂ) := by
  have h := (multipliable_real_qEulerProduct_factors hq0 hq1).map_tprod
    Complex.ofRealHom Complex.continuous_ofReal
  simpa [qEulerProduct] using h.symm

theorem real_qEulerProduct_pos {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 < ∏' n : ℕ, (1 - q ^ (n + 1)) := by
  have hs : Summable (fun n : ℕ => -(q ^ (n + 1))) := by
    simpa only [pow_succ] using ((summable_geometric_of_lt_one hq0 hq1).mul_right q).neg
  have hlog : Summable (fun n : ℕ => Real.log (1 - q ^ (n + 1))) := by
    simpa only [sub_eq_add_neg] using Real.summable_log_one_add_of_summable hs
  have hpos (n : ℕ) : 0 < 1 - q ^ (n + 1) :=
    sub_pos.mpr (pow_lt_one₀ hq0 hq1 (by omega))
  rw [← Real.rexp_tsum_eq_tprod hpos hlog]
  exact Real.exp_pos _

end DirichletL

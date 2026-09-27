import Analysis.QProductAnalytic

/-!
The Euler q-product in DLMF 27.14.2 and the product algebra needed for
Dedekind eta (DLMF 27.14.12). All analytic assertions use the open unit disk.
-/

namespace DirichletL

/-- The positive-index Euler q-product, used in DLMF 27.14.12 to define eta. -/
noncomputable def qEulerProduct (q : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ (n + 1))

@[simp] theorem qEulerProduct_zero : qEulerProduct 0 = 1 := by
  simp [qEulerProduct]

theorem multipliable_qEulerProduct_factors {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable (fun n : ℕ => 1 - q ^ (n + 1)) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using
    multipliable_one_add_mul_pow (s := (-1 : ℂ)) (e := fun n => n + 1)
      (by norm_num) (fun _ => le_rfl) hq

theorem qEulerProduct_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : qEulerProduct q ≠ 0 := by
  simpa only [qEulerProduct, neg_one_mul, sub_eq_add_neg] using
    tprod_one_add_mul_pow_ne_zero (s := (-1 : ℂ)) (e := fun n => n + 1)
      (by norm_num) (fun _ => le_rfl) hq

theorem differentiableOn_qEulerProduct :
    DifferentiableOn ℂ qEulerProduct (Metric.ball 0 1) := by
  simpa only [qEulerProduct, neg_one_mul, sub_eq_add_neg] using
    differentiableOn_tprod_one_add_mul_pow (s := (-1 : ℂ)) (e := fun n => n + 1)
      (by norm_num) (fun _ => le_rfl)

theorem tprod_one_sub_pow_mul_one_add_pow {q : ℂ} {e : ℕ → ℕ}
    (he : ∀ i, i + 1 ≤ e i) (hq : ‖q‖ < 1) :
    (∏' i, (1 - q ^ e i)) * (∏' i, (1 + q ^ e i)) =
      ∏' i, (1 - (q ^ 2) ^ e i) := by
  have hm : Multipliable (fun i => 1 - q ^ e i) := by
    simpa only [neg_one_mul, sub_eq_add_neg] using
      multipliable_one_add_mul_pow (s := (-1 : ℂ)) (by norm_num) he hq
  have hp : Multipliable (fun i => 1 + q ^ e i) := by
    simpa only [one_mul] using
      multipliable_one_add_mul_pow (s := (1 : ℂ)) (by norm_num) he hq
  rw [← hm.tprod_mul hp]
  apply tprod_congr
  intro i
  rw [pow_right_comm q 2 (e i)]
  ring

theorem tprod_odd_mul_qEulerProduct_sq {q : ℂ} (hq : ‖q‖ < 1) :
    (∏' i : ℕ, (1 - q ^ (2 * i + 1))) * qEulerProduct (q ^ 2) =
      qEulerProduct q := by
  have he : Multipliable (fun i : ℕ => 1 - q ^ (2 * i + 1)) := by
    simpa only [neg_one_mul, sub_eq_add_neg] using
      multipliable_one_add_mul_pow (s := (-1 : ℂ)) (e := fun i => 2 * i + 1)
        (by norm_num) (by intro i; dsimp only; omega) hq
  have ho : Multipliable (fun i : ℕ => 1 - q ^ (2 * i + 1 + 1)) := by
    simpa only [neg_one_mul, sub_eq_add_neg] using
      multipliable_one_add_mul_pow (s := (-1 : ℂ)) (e := fun i => 2 * i + 1 + 1)
        (by norm_num) (by intro i; dsimp only; omega) hq
  have hsq : qEulerProduct (q ^ 2) = ∏' i : ℕ, (1 - q ^ (2 * i + 1 + 1)) := by
    apply tprod_congr
    intro i
    rw [← pow_mul]
    congr 2
  rw [hsq]
  exact tprod_even_mul_odd (f := fun i : ℕ => 1 - q ^ (i + 1)) he ho

end DirichletL

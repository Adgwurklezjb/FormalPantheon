import Mathlib

/-!
Finite coefficient comparisons used to establish local convergence of the
Hauptmodul in CDT v2, Section 11.1, equation `haupt`. See
-/

namespace DirichletL

theorem abs_coeff_mul_le_of_bounds {f g F G : PowerSeries ℤ}
    (hf : ∀ n, |PowerSeries.coeff (R := ℤ) n f| ≤ PowerSeries.coeff (R := ℤ) n F)
    (hg : ∀ n, |PowerSeries.coeff (R := ℤ) n g| ≤ PowerSeries.coeff (R := ℤ) n G) (n : ℕ) :
    |PowerSeries.coeff (R := ℤ) n (f * g)| ≤ PowerSeries.coeff (R := ℤ) n (F * G) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro p hp
  rw [abs_mul]
  exact mul_le_mul (hf p.1) (hg p.2) (abs_nonneg _) ((abs_nonneg _).trans (hf p.1))

theorem abs_coeff_pow_le_of_bounds {f F : PowerSeries ℤ}
    (hf : ∀ n, |PowerSeries.coeff (R := ℤ) n f| ≤ PowerSeries.coeff (R := ℤ) n F) (k n : ℕ) :
    |PowerSeries.coeff (R := ℤ) n (f ^ k)| ≤ PowerSeries.coeff (R := ℤ) n (F ^ k) := by
  induction k generalizing n with
  | zero => simp only [pow_zero, PowerSeries.coeff_one]; split_ifs <;> norm_num
  | succ k ih =>
    simpa only [pow_succ] using abs_coeff_mul_le_of_bounds ih hf n

theorem abs_coeff_prod_le_of_bounds {ι : Type*} (s : Finset ι)
    {f F : ι → PowerSeries ℤ}
    (hf : ∀ i ∈ s, ∀ n, |PowerSeries.coeff (R := ℤ) n (f i)| ≤ PowerSeries.coeff (R := ℤ) n (F i))
    (n : ℕ) :
    |PowerSeries.coeff (R := ℤ) n (∏ i ∈ s, f i)| ≤ PowerSeries.coeff (R := ℤ) n (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => simp only [Finset.prod_empty, PowerSeries.coeff_one]; split_ifs <;> norm_num
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact abs_coeff_mul_le_of_bounds (hf i (Finset.mem_insert_self _ _))
      (fun m => ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) m) n

end DirichletL

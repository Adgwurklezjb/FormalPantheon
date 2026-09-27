import Arithmetic.PowerSeriesMajorants
import Analysis.Hauptmodul

/-!
Uniform coefficient bounds for the theta products in CDT v2 Section 11.1.
The geometric majorant justifies their local complex evaluation; see
-/

namespace DirichletL

private theorem abs_coeff_prod_degree_le_four_pow {f : ℕ → PowerSeries ℤ}
    (hf : ∀ i n, |PowerSeries.coeff (R := ℤ) n (f i)| ≤ 1) (n : ℕ) :
    |PowerSeries.coeff (R := ℤ) n (∏ i ∈ Finset.range (n + 1), f i)| ≤ 4 ^ n := by
  have h := abs_coeff_prod_le_of_bounds (Finset.range (n + 1))
    (F := fun _ => PowerSeries.mk 1) (fun i _ m => by simpa using hf i m) n
  simp only [Finset.prod_const, Finset.card_range,
    PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_mk] at h
  refine h.trans ?_
  cases n with
  | zero => norm_num
  | succ n =>
    have hc := Nat.choose_le_two_pow (n + 1 + (n + 1)) (n + 1)
    have he : 2 ^ (n + 1 + (n + 1)) = 4 ^ (n + 1) := by
      rw [show n + 1 + (n + 1) = 2 * (n + 1) by omega, pow_mul]
      norm_num
    rw [he] at hc
    exact_mod_cast hc

theorem abs_coeff_prod_range_le_four_pow {f : ℕ → PowerSeries ℤ}
    (hf : ∀ i, PowerSeries.X ^ (i + 1) ∣ f i - 1)
    (hc : ∀ i n, |PowerSeries.coeff (R := ℤ) n (f i)| ≤ 1) (N n : ℕ) :
    |PowerSeries.coeff (R := ℤ) n (∏ i ∈ Finset.range N, f i)| ≤ 4 ^ n := by
  classical
  by_cases hN : N ≤ n + 1
  · let g : ℕ → PowerSeries ℤ := fun i => if i < N then f i else 1
    have hg : ∀ i m, |PowerSeries.coeff (R := ℤ) m (g i)| ≤ 1 := by
      intro i m
      dsimp [g]
      split_ifs
      · exact hc i m
      · simp only [PowerSeries.coeff_one]
        split_ifs <;> norm_num
    have he : (∏ i ∈ Finset.range N, f i) = ∏ i ∈ Finset.range (n + 1), g i := by
      apply Finset.prod_subset_one_on_sdiff (Finset.range_mono hN)
      · intro i hi
        simp only [Finset.mem_sdiff, Finset.mem_range] at hi
        simp [g, hi.2]
      · intro i hi
        simp [g, Finset.mem_range.mp hi]
    rw [he]
    exact abs_coeff_prod_degree_le_four_pow hg n
  · obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    rw [coeff_formalProduct_stable hf (by omega : n ≤ M)]
    exact abs_coeff_prod_degree_le_four_pow hc n

theorem abs_coeff_formalProduct_le_four_pow {f : ℕ → PowerSeries ℤ}
    (hc : ∀ i n, |PowerSeries.coeff (R := ℤ) n (f i)| ≤ 1) (n : ℕ) :
    |PowerSeries.coeff (R := ℤ) n (formalProduct f)| ≤ 4 ^ n := by
  rw [coeff_formalProduct]
  exact abs_coeff_prod_degree_le_four_pow hc n

end DirichletL

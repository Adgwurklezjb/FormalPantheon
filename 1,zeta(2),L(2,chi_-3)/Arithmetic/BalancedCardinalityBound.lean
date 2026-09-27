import Arithmetic.MultinomialMaxima
import Arithmetic.BalancedMapCardinality

/-!
CDT v2, balanced-indices lemma, supplied TeX 3806-3823.
The exact profile count and multinomial expansion give the strict
lower bound when the number of species exceeds one and the block is positive.
-/

namespace DirichletL

open scoped Nat

theorem card_piAntidiag_univ_nat (m n : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset (Fin m)) n).card =
      (m + n - 1).choose n := by
  rw [← Finset.map_sym_eq_piAntidiag, Finset.card_map, Finset.sym_univ,
    Finset.card_univ]
  simpa using Sym.card_sym_eq_choose (α := Fin m) n

theorem card_piAntidiag_univ_nat_of_pos {m : ℕ} (hm : 0 < m) (n : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset (Fin m)) n).card =
      (n + m - 1).choose (m - 1) := by
  rw [card_piAntidiag_univ_nat, Nat.add_comm m n]
  exact Nat.choose_symm_of_eq_add (by omega)

theorem sum_multinomial_piAntidiag (m n : ℕ) :
    (∑ f ∈ Finset.piAntidiag (Finset.univ : Finset (Fin m)) n,
      Nat.multinomial Finset.univ f) = m ^ n := by
  simpa using (Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin m))
    (fun _ => (1 : ℕ)) n).symm

theorem multinomial_single_profile {m : ℕ} (n : ℕ) (i : Fin m) :
    Nat.multinomial Finset.univ (fun j : Fin m => if j = i then n else 0) = 1 := by
  simp [Nat.multinomial, apply_ite]
  exact Nat.div_self (Nat.factorial_pos n)

theorem one_lt_multinomial_const {m h : ℕ} (hm : 1 < m) (hh : 0 < h) :
    1 < Nat.multinomial Finset.univ (fun _ : Fin m => h) := by
  let i : Fin m := ⟨0, by omega⟩
  let j : Fin m := ⟨1, hm⟩
  have hij : i ≠ j := by simp [i, j]
  let f : Fin m → ℕ := fun k => if k = i then m * h else 0
  have hf : (∑ k : Fin m, f k) = m * h := by simp [f]
  have hprod : (∏ k : Fin m, (f k)!) = (m * h)! := by simp [f, apply_ite]
  have hh' : 1 ≤ h := hh
  have hN : 1 < m * h := hm.trans_le (by simpa using Nat.mul_le_mul_left m hh')
  have hgap : f j + 1 < f i := by simpa [f, hij.symm] using hN
  let u : Fin m → ℕ := Function.update (Function.update f i (f i - 1)) j (f j + 1)
  have hu : (∑ k : Fin m, u k) = m * h :=
    (sum_update_transfer f i j hij (by omega)).trans hf
  have hlt := prod_factorial_update_transfer_lt f i j hgap
  change (∏ k : Fin m, (u k)!) < ∏ k : Fin m, (f k)! at hlt
  rw [hprod] at hlt
  have hden : (h !) ^ m < (m * h)! :=
    (prod_factorial_const_le_of_sum_eq u hu).trans_lt hlt
  have hspec : (h !) ^ m * Nat.multinomial Finset.univ (fun _ : Fin m => h) =
      (m * h)! := by
    simpa using Nat.multinomial_spec Finset.univ (fun _ : Fin m => h)
  by_contra hnot
  have hc : Nat.multinomial Finset.univ (fun _ : Fin m => h) ≤ 1 := le_of_not_gt hnot
  have hle := Nat.mul_le_mul_left ((h !) ^ m) hc
  rw [mul_one, hspec] at hle
  exact (not_lt_of_ge hle) hden

theorem pow_lt_card_balancedSpeciesIndices_mul_choose {m h : ℕ}
    (hm : 1 < m) (hh : 0 < h) :
    m ^ (m * h) < (balancedSpeciesIndices m h).card *
      (m * h + m - 1).choose (m - 1) := by
  classical
  let s := Finset.piAntidiag (Finset.univ : Finset (Fin m)) (m * h)
  let i : Fin m := ⟨0, by omega⟩
  let g : Fin m → ℕ := fun j => if j = i then m * h else 0
  have hg : g ∈ s := by simp [s, g, Finset.mem_piAntidiag]
  have hgcoeff : Nat.multinomial Finset.univ g = 1 := multinomial_single_profile _ i
  have hstrict : (∑ f ∈ s, Nat.multinomial Finset.univ f) <
      ∑ _f ∈ s, Nat.multinomial Finset.univ (fun _ : Fin m => h) := by
    apply Finset.sum_lt_sum
    · intro f hf
      exact multinomial_le_const_of_sum_eq f (Finset.mem_piAntidiag.mp hf).1
    · exact ⟨g, hg, by rw [hgcoeff]; exact one_lt_multinomial_const hm hh⟩
  calc
    _ = ∑ f ∈ s, Nat.multinomial Finset.univ f := (sum_multinomial_piAntidiag m (m * h)).symm
    _ < ∑ _f ∈ s, Nat.multinomial Finset.univ (fun _ : Fin m => h) := hstrict
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, s,
        card_piAntidiag_univ_nat_of_pos (by omega : 0 < m),
        card_balancedSpeciesIndices_eq_multinomial]
      exact Nat.mul_comm _ _

theorem div_choose_lt_card_balancedSpeciesIndices {m h : ℕ}
    (hm : 1 < m) (hh : 0 < h) :
    (m : ℝ) ^ (m * h) / ((m * h + m - 1).choose (m - 1) : ℝ) <
      ((balancedSpeciesIndices m h).card : ℝ) := by
  have hp : 0 < ((m * h + m - 1).choose (m - 1) : ℝ) := by
    exact_mod_cast (Nat.choose_pos (by omega : m - 1 ≤ m * h + m - 1))
  apply (div_lt_iff₀ hp).2
  exact_mod_cast pow_lt_card_balancedSpeciesIndices_mul_choose hm hh

theorem pow_lt_card_balancedSpeciesIndices_mul_pow {m h : ℕ}
    (hm : 1 < m) (hh : 0 < h) :
    m ^ (m * h) < (balancedSpeciesIndices m h).card * (m * h + m - 1) ^ (m - 1) :=
  (pow_lt_card_balancedSpeciesIndices_mul_choose hm hh).trans_le
    (Nat.mul_le_mul_left _ (Nat.choose_le_pow _ _))

theorem card_balancedSpeciesIndices_le_pow (m h : ℕ) :
    (balancedSpeciesIndices m h).card ≤ m ^ (m * h) := by
  calc
    _ ≤ Fintype.card (Fin (m * h) → Fin m) := Finset.card_le_univ _
    _ = _ := by simp

end DirichletL

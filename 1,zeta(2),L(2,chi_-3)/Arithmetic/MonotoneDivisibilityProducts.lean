import Arithmetic.Denominators

/-!
The finite selection argument in CDT v2, supplied TeX 4304-4404.
Sorted selected indices are bounded by the final indices, so a chain
under divisibility has one product cap for every selection of that size.
-/

namespace DirichletL

theorem orderEmbedding_fin_val_le_tail {r d : ℕ} (f : Fin r ↪o Fin d) (i : Fin r) :
    (f i : ℕ) ≤ d - r + (i : ℕ) := by
  let g : Set.Ici i → Set.Ici (f i) := fun j => ⟨f j.1, f.monotone j.2⟩
  have hg : Function.Injective g := by
    intro j k h
    apply Subtype.ext
    exact f.injective (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_Ici, Fin.card_Ici] at hcard
  have hi := i.isLt
  have hfi := (f i).isLt
  omega

theorem prod_subset_dvd_tail_of_dvd_monotone {d : ℕ} (s : Finset (Fin d))
    (a : ℕ → ℕ) (ha : ∀ i j : ℕ, i ≤ j → j < d → a i ∣ a j) :
    (∏ i ∈ s, a (i : ℕ)) ∣ ∏ j ∈ Finset.range s.card, a (d - s.card + j) := by
  have hcard : s.card ≤ d := by simpa only [Fintype.card_fin] using s.card_le_univ
  have hp : (∏ i ∈ s, a (i : ℕ)) =
      ∏ i : Fin s.card, a (s.orderEmbOfFin rfl i : ℕ) := by
    simpa only [Finset.map_orderEmbOfFin_univ] using
      Finset.prod_map Finset.univ (s.orderEmbOfFin rfl).toEmbedding (fun i : Fin d => a (i : ℕ))
  rw [hp, Finset.prod_range]
  apply Finset.prod_dvd_prod_of_dvd
  intro i _
  apply ha _ _ (orderEmbedding_fin_val_le_tail (s.orderEmbOfFin rfl) i)
  have hi := i.isLt
  omega

theorem prod_lcmPrefix_subset_dvd_tail {d : ℕ} (s : Finset (Fin d))
    (b : ℕ) (n : ℕ → ℕ) (hn : MonotoneOn n (Set.Iio d)) :
    (∏ i ∈ s, lcmPrefix (b * n (i : ℕ))) ∣
      ∏ j ∈ Finset.range s.card, lcmPrefix (b * n (d - s.card + j)) := by
  apply prod_subset_dvd_tail_of_dvd_monotone s (fun j => lcmPrefix (b * n j))
  intro i j hij hj
  exact lcmPrefix_dvd (Nat.mul_le_mul_left b (hn (hij.trans_lt hj) hj hij))

theorem prod_lcmPrefix_subset_dvd_tail_of_le {d : ℕ} (s : Finset (Fin d))
    (b : ℕ) (n N : ℕ → ℕ) (hn : ∀ i < d, n i ≤ N i)
    (hN : MonotoneOn N (Set.Iio d)) :
    (∏ i ∈ s, lcmPrefix (b * n (i : ℕ))) ∣
      ∏ j ∈ Finset.range s.card, lcmPrefix (b * N (d - s.card + j)) := by
  have hfirst : (∏ i ∈ s, lcmPrefix (b * n (i : ℕ))) ∣
      ∏ i ∈ s, lcmPrefix (b * N (i : ℕ)) := by
    apply Finset.prod_dvd_prod_of_dvd
    intro i _
    exact lcmPrefix_dvd (Nat.mul_le_mul_left b (hn i i.isLt))
  exact hfirst.trans (prod_lcmPrefix_subset_dvd_tail s b N hN)

end DirichletL

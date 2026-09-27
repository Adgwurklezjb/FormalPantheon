import Analysis.Holonomy

/-!
Exact balanced species counts in CDT v2, supplied TeX 3770-3826,
4304-4404, and 4440-4518. Zero-based finite rows are converted to
the one-based denominator and integration arrays explicitly.
-/

namespace DirichletL

theorem sum_cdt14_species_of_balanced {h : ℕ} (σ : ℕ → Fin 14)
    (hσ : ∀ i : Fin 14, ((Finset.univ : Finset (Fin (14 * h))).filter
      (fun j : Fin (14 * h) => σ (j : ℕ) = i)).card = h) (w : Fin 14 → ℕ) :
    (∑ j ∈ Finset.range (14 * h), w (σ j)) = h * ∑ i : Fin 14, w i := by
  rw [Finset.sum_range]
  rw [← Finset.sum_fiberwise' (Finset.univ : Finset (Fin (14 * h)))
    (fun j : Fin (14 * h) => σ (j : ℕ)) w]
  simp only [Finset.sum_const, hσ, nsmul_eq_mul]
  exact (Finset.mul_sum _ _ _).symm

theorem card_cdt14_first_column_of_balanced {h : ℕ} (σ : ℕ → Fin 14)
    (hσ : ∀ i : Fin 14, ((Finset.univ : Finset (Fin (14 * h))).filter
      (fun j : Fin (14 * h) => σ (j : ℕ) = i)).card = h) :
    ((Finset.univ : Finset (Fin (14 * h))).filter (fun j : Fin (14 * h) => σ (j : ℕ) ≠ 0)).card = 13 * h := by
  have hrows : ((Finset.univ : Finset (Fin 14)).erase 0).card = 13 := by decide
  have hc := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin (14 * h))) ((Finset.univ : Finset (Fin 14)).erase 0)
    (fun j : Fin (14 * h) => σ (j : ℕ))
  simpa only [hσ, Finset.sum_const, hrows, nsmul_eq_mul,
    Finset.mem_erase, Finset.mem_univ, and_true] using hc.symm

theorem card_cdt14_second_column_of_balanced {h : ℕ} (σ : ℕ → Fin 14)
    (hσ : ∀ i : Fin 14, ((Finset.univ : Finset (Fin (14 * h))).filter
      (fun j : Fin (14 * h) => σ (j : ℕ) = i)).card = h) :
    ((Finset.univ : Finset (Fin (14 * h))).filter
      (fun j : Fin (14 * h) => 3 ≤ (σ (j : ℕ) : ℕ))).card = 11 * h := by
  let rows : Finset (Fin 14) := Finset.univ.filter (fun i : Fin 14 => 3 ≤ (i : ℕ))
  have hrows : rows.card = 11 := by decide
  have hc := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin (14 * h))) rows (fun j : Fin (14 * h) => σ (j : ℕ))
  simp only [hσ, Finset.sum_const, hrows, nsmul_eq_mul] at hc
  simpa only [rows, Finset.mem_filter, Finset.mem_univ, true_and] using hc.symm

theorem sum_cdt14_exponents_of_balanced {h : ℕ} (σ : ℕ → Fin 14)
    (hσ : ∀ i : Fin 14, ((Finset.univ : Finset (Fin (14 * h))).filter
      (fun j : Fin (14 * h) => σ (j : ℕ) = i)).card = h) :
    (∑ j ∈ Finset.range (14 * h), cdtIntegrationExponents ((σ j : ℕ) + 1)) = 6 * h := by
  have hi := integrationExponentSum_cdt14
  change (∑ i ∈ Finset.range 14, cdtIntegrationExponents (i + 1)) = 6 at hi
  rw [Finset.sum_range] at hi
  rw [sum_cdt14_species_of_balanced σ hσ (fun i => cdtIntegrationExponents ((i : ℕ) + 1)), hi]
  omega

end DirichletL

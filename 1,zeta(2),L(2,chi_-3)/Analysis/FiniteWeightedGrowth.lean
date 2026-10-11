import Analysis.BlockPhaseApproximation

/-!
The explicit finite good-block exponent in CDT v2, supplied TeX 4130-4228.
Meanings and the independent signed calculation precede these bodies
-/

namespace DirichletL

/-- The finite regular-grid growth exponent with separate phase and weight errors. -/
noncomputable def blockGridGrowth {κ : Type*} [DecidableEq κ] {d : ℕ}
    (b : Fin d → κ) (f : κ → ℝ → ℝ) (D ξ ε B : ℝ) : ℝ :=
  D * sortedGridSum (blockGridValues b f) + D * d * (ξ + ε * B)

theorem neg_mul_le_blockGridGrowth {κ : Type*} [DecidableEq κ] {d : ℕ}
    (b : Fin d → κ) (f : κ → ℝ → ℝ) {D ξ ε B : ℝ}
    (hD : 0 ≤ D) (hξ : 0 ≤ ξ) (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hfB : ∀ q u, u ∈ Set.Icc (0 : ℝ) 1 → |f q u| ≤ B) :
    -D * d * B ≤ blockGridGrowth b f D ξ ε B := by
  have h := (abs_le.mp (abs_sortedGridSum_le (blockGridValues b f)
    (abs_blockGridValues_le b f hfB))).1
  have herr : 0 ≤ D * d * (ξ + ε * B) := by positivity
  have hmul := mul_le_mul_of_nonneg_left h hD
  dsimp only [blockGridGrowth]
  nlinarith

theorem exists_block_weighted_growth_bound {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : κ → ℝ → ℝ) (hf : ∀ q, ContinuousOn (f q) (Set.Icc (0 : ℝ) 1))
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ η : ℝ, 0 < η ∧ ∀ d : ℕ, ∀ b : Fin d → κ, ∀ s : Fin d → ℝ,
      (∀ j, s j ∈ Set.Icc (0 : ℝ) 1) →
      (∀ q, HasIntervalDiscrepancyLE
        (fun i => s ((Finset.univ.filter (fun j => b j = q)).orderEmbOfFin rfl i)) η) →
      ∀ t : Fin d → ℝ, ∀ ε B : ℝ, HasIntervalDiscrepancyLE t ε →
      (∀ j, t j ∈ Set.Icc (0 : ℝ) 1) →
      (∀ q u, u ∈ Set.Icc (0 : ℝ) 1 → |f q u| ≤ B) →
      ∑ j, t j * f (b j) (s j) ≤
        sortedGridSum (blockGridValues b f) + d * (ξ + ε * B) := by
  obtain ⟨η, hη, hphase⟩ := exists_block_phase_approximation f hf hξ
  refine ⟨η, hη, ?_⟩
  intro d b s hs hgood t ε B ht htcube hB
  obtain ⟨τ, hlabel, hclose⟩ := hphase d b s hs hgood
  have hgrid := (ht.comp_perm τ).sum_mul_le_sortedGridSum
    (fun i => htcube (τ i)) (blockGridValues b f) (abs_blockGridValues_le b f hB)
  calc
    _ = ∑ j, t (τ j) * f (b j) (s (τ j)) := by
      simpa only [hlabel] using
        (Equiv.sum_comp τ (fun j => t j * f (b j) (s j))).symm
    _ ≤ ∑ j, (t (τ j) * blockGridValues b f j + ξ) := by
      apply Finset.sum_le_sum
      intro j _
      have hdiff := mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (hclose j)) (htcube (τ j)).1
      have hξmul := mul_le_of_le_one_left hξ.le (htcube (τ j)).2
      nlinarith
    _ = (∑ j, t (τ j) * blockGridValues b f j) + d * ξ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    _ ≤ _ := by simpa only [Function.comp_apply] using add_le_add_right hgrid (d * ξ)
    _ = _ := by ring

theorem exists_scaled_block_weighted_growth_bound {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : κ → ℝ → ℝ) (hf : ∀ q, ContinuousOn (f q) (Set.Icc (0 : ℝ) 1))
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ η : ℝ, 0 < η ∧ ∀ d : ℕ, ∀ b : Fin d → κ, ∀ s : Fin d → ℝ,
      (∀ j, s j ∈ Set.Icc (0 : ℝ) 1) →
      (∀ q, HasIntervalDiscrepancyLE
        (fun i => s ((Finset.univ.filter (fun j => b j = q)).orderEmbOfFin rfl i)) η) →
      ∀ D : ℝ, 0 < D → ∀ k : Fin d → ℝ, ∀ ε B : ℝ,
      HasIntervalDiscrepancyLE (fun j => k j / D) ε →
      (∀ j, k j ∈ Set.Icc (0 : ℝ) D) →
      (∀ q u, u ∈ Set.Icc (0 : ℝ) 1 → |f q u| ≤ B) →
      ∑ j, k j * f (b j) (s j) ≤ blockGridGrowth b f D ξ ε B := by
  obtain ⟨η, hη, hnormalized⟩ := exists_block_weighted_growth_bound f hf hξ
  refine ⟨η, hη, ?_⟩
  intro d b s hs hgood D hD k ε B hk hkcube hB
  have hc (j : Fin d) : k j / D ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (hkcube j).1 hD.le, (div_le_one hD).mpr (hkcube j).2⟩
  have hbound := mul_le_mul_of_nonneg_left
    (hnormalized d b s hs hgood (fun j => k j / D) ε B hk hc hB) hD.le
  have hcancel (j : Fin d) : D * (k j / D * f (b j) (s j)) = k j * f (b j) (s j) := by
    field_simp
  simpa only [Finset.mul_sum, hcancel, blockGridGrowth, mul_add, mul_assoc] using hbound

end DirichletL

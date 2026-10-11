import Analysis.BlockGridValues
import Analysis.FiniteRearrangement

/-!
Uniform phase comparison for CDT v2, supplied TeX 4160-4228.
The continuity replacement of the pointwise bounded-variation estimate is
-/

namespace DirichletL

theorem exists_uniform_profile_tolerance {κ : Type*} [Fintype κ]
    (f : κ → ℝ → ℝ) (hf : ∀ q, ContinuousOn (f q) (Set.Icc (0 : ℝ) 1))
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ η : ℝ, 0 < η ∧ ∀ q s, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ u, u ∈ Set.Icc (0 : ℝ) 1 → |s - u| ≤ η → |f q s - f q u| ≤ ξ := by
  have hc : ContinuousOn (fun u q => f q u) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_pi.mpr hf
  obtain ⟨η, hη, hclose⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) ξ hξ
  refine ⟨η, hη, ?_⟩
  intro q s hs u hu hsu
  simpa only [Real.dist_eq] using
    (dist_le_pi_dist (fun q => f q s) (fun q => f q u) q).trans
      (hclose s hs u hu (by simpa only [Real.dist_eq] using hsu))

theorem exists_block_phase_approximation {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : κ → ℝ → ℝ) (hf : ∀ q, ContinuousOn (f q) (Set.Icc (0 : ℝ) 1))
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ η : ℝ, 0 < η ∧ ∀ d : ℕ, ∀ b : Fin d → κ, ∀ s : Fin d → ℝ,
      (∀ j, s j ∈ Set.Icc (0 : ℝ) 1) →
      (∀ q, HasIntervalDiscrepancyLE
        (fun i => s ((Finset.univ.filter (fun j => b j = q)).orderEmbOfFin rfl i)) η) →
      ∃ τ : Equiv.Perm (Fin d), (∀ j, b (τ j) = b j) ∧
        ∀ j, |f (b j) (s (τ j)) - blockGridValues b f j| ≤ ξ := by
  obtain ⟨η, hη, hclose⟩ := exists_uniform_profile_tolerance f hf hξ
  refine ⟨η, hη, ?_⟩
  intro d b s hs hgood
  let σ (q : κ) := Tuple.sort
    (fun i => s ((Finset.univ.filter (fun j => b j = q)).orderEmbOfFin rfl i))
  obtain ⟨τ, hτ, hlabel⟩ := exists_perm_block_orderEmbOfFin b σ
  refine ⟨τ, hlabel, ?_⟩
  intro j
  obtain ⟨⟨q, i⟩, rfl⟩ := (blockIndexEquiv b).surjective j
  rw [blockIndexEquiv_label b q i, blockIndexEquiv_apply b q i, hτ q i,
    blockGridValues_orderEmbOfFin]
  have hn : 0 < ((Finset.univ.filter (fun j => b j = q)).card : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  apply hclose q _ (hs _) _
    ⟨by positivity, (div_le_one hn).mpr (by exact_mod_cast Nat.succ_le_of_lt i.isLt)⟩
  exact ((hgood q).comp_perm (σ q)).abs_coordinate_sub_grid_le
    (fun i => hs _) (Tuple.monotone_sort _) i

end DirichletL

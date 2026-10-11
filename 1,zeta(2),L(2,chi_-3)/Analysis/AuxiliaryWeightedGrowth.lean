import Analysis.AuxiliaryParameterIndices
import Analysis.CircleLogProfile
import Analysis.FiniteWeightedGrowth

/-!
The original auxiliary exponents in CDT v2, supplied TeX 3950-4004,
3998-4028, and 4130-4228. Meanings and the explicit exponent-gap calculation
-/

namespace DirichletL

open scoped Classical

theorem exists_auxiliary_block_weighted_growth_bound {κ : Type*}
    [Fintype κ] [DecidableEq κ] (ψ : κ → ℂ → ℂ)
    (hψ : ∀ q, ContinuousOn (ψ q) (Metric.closedBall 0 1))
    (hne : ∀ q (z : ℂ), ‖z‖ = 1 → ψ q z ≠ 0) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ η : ℝ, 0 < η ∧ ∀ (m h D : ℕ) (ε : ℝ), 0 < D →
      ∀ b : Fin (m * h) → κ, ∀ θ : Fin (m * h) → AddCircle (2 * Real.pi),
      (∀ q, HasIntervalDiscrepancyLE
        (fun i => torusUnitRepresentative
          (θ ((Finset.univ.filter (fun j => b j = q)).orderEmbOfFin rfl i))) η) →
      ∀ B : ℝ, (∀ q u, u ∈ Set.Icc (0 : ℝ) 1 → |circleLogProfile (ψ q) u| ≤ B) →
      ∀ π : Equiv.Perm (Fin (m * h)), ∀ v : ↥(auxiliaryFreeIndices m h D ε),
        ∑ j, ((v.val.2 (π j)).val : ℝ) * Real.log ‖ψ (b j) (fourier 1 (θ j))‖ ≤
          blockGridGrowth b (fun q => circleLogProfile (ψ q)) D ξ ε B := by
  obtain ⟨η, hη, hscaled⟩ := exists_scaled_block_weighted_growth_bound
    (fun q => circleLogProfile (ψ q))
    (fun q => (continuous_circleLogProfile (hψ q) (hne q)).continuousOn) hξ
  refine ⟨η, hη, ?_⟩
  intro m h D ε hD b θ hgood B hB π v
  have hs (j : Fin (m * h)) : torusUnitRepresentative (θ j) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(torusUnitRepresentative_mem_Ico _).1, (torusUnitRepresentative_mem_Ico _).2.le⟩
  have hk := ((mem_auxiliaryFreeIndices.mp v.property).2).comp_perm π
  have hc (j : Fin (m * h)) : ((v.val.2 (π j)).val : ℝ) ∈ Set.Icc (0 : ℝ) D :=
    ⟨Nat.cast_nonneg _, by exact_mod_cast (Nat.le_of_lt (v.val.2 (π j)).isLt)⟩
  simpa only [circleLogProfile_torusUnitRepresentative] using
    hscaled (m * h) b (fun j => torusUnitRepresentative (θ j)) hs hgood D
      (by exact_mod_cast hD) (fun j => ((v.val.2 (π j)).val : ℝ)) ε B hk hc hB

theorem damped_exponent_le_of_blockGridGrowth {κ : Type*} [DecidableEq κ] {d : ℕ}
    (b : Fin d → κ) (f : κ → ℝ → ℝ) {D ξ ε B c M : ℝ}
    (hd : 0 < d) (hc : 0 < c) (hD : 0 ≤ D) (hξ : 0 ≤ ξ) (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hfB : ∀ q u, u ∈ Set.Icc (0 : ℝ) 1 → |f q u| ≤ B)
    (hM : M ≤ max 0 ((d : ℝ) * D * B - blockGridGrowth b f D ξ ε B) /
      (c * (d : ℝ) ^ 2) + 2) : M ≤ (2 * B / c) * D / d + 2 := by
  have hneg := neg_mul_le_blockGridGrowth b f hD hξ hε hB hfB
  have hgap : max 0 ((d : ℝ) * D * B - blockGridGrowth b f D ξ ε B) ≤
      2 * D * d * B := max_le (by positivity) (by nlinarith)
  calc
    M ≤ _ := hM
    _ ≤ 2 * D * d * B / (c * (d : ℝ) ^ 2) + 2 :=
      add_le_add_right (div_le_div_of_nonneg_right hgap (by positivity)) 2
    _ = _ := by field_simp

end DirichletL

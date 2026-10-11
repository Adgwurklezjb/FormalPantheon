import Analysis.AuxiliaryWeightedGrowth
import Analysis.DampedAuxiliaryGrowth

/-!
The finite grid coefficient bound for CDT v2, supplied TeX 3998-4028
and 4069-4228, and published UDC equations 2.5.15-2.5.24. The literal

The continuation interface is recorded before this revision in
-/

namespace DirichletL

open scoped Classical Topology

theorem exists_damped_auxiliary_family_grid_bound {κ : Type*}
    [Fintype κ] [DecidableEq κ] {m : ℕ}
    (f : Fin m → PowerSeries ℚ) (F : Fin m → ℂ → ℂ)
    (φ : κ → PowerSeries ℂ) (ψ : κ → ℂ → ℂ)
    (P : Fin m → κ → ℂ → ℂ) (H : Polynomial ℂ)
    (hf : ∀ i, HasFPowerSeriesAt (F i) (complexSeries (f i)) 0)
    (hψ : ∀ q, HasFPowerSeriesAt (ψ q)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n (φ q))) 0)
    (hφ : ∀ q, PowerSeries.constantCoeff (R := ℂ) (φ q) = 0)
    (hP : ∀ i q, P i q =ᶠ[𝓝 (0 : ℂ)] fun z => F i (ψ q z))
    (hdψ : ∀ q, AnalyticOnNhd ℂ (ψ q) (Metric.closedBall 0 1))
    (hH : ∀ i q, AnalyticOnNhd ℂ (fun z => H.eval z * P i q z)
      (Metric.closedBall 0 1))
    (hne : ∀ q (z : ℂ), ‖z‖ = 1 → ψ q z ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, ∀ ξ ρ : ℝ, 0 < ξ → 0 < ρ →
      ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ (h D : ℕ) (ε : ℝ), N ≤ m * h →
      0 < D → 0 ≤ ε → ∀ b : Fin (m * h) → κ,
      (∀ q, ρ * (m * h : ℕ) ≤ ((Finset.univ.filter (fun j => b j = q)).card : ℝ)) →
      ∀ (t : ↥(auxiliaryFreeIndices m h D ε) → ℤ) (π : Equiv.Perm (Fin (m * h)))
        (S : ℝ), (∀ v, ‖(t v : ℂ)‖ ≤ Real.exp S) →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ (2 * B / c) * D / (m * h : ℕ) + 2 ∧
        blockVandermondePolynomial (R := ℂ) b M ≠ 0 ∧
        ∀ n : Fin (m * h) →₀ ℕ,
        ‖MvPowerSeries.coeff (R := ℂ) n
          ((blockVandermondePolynomial (R := ℂ) b M : MvPowerSeries (Fin (m * h)) ℂ) *
            ((∏ j, powerSeriesInVariable ℂ j (H : PowerSeries ℂ)) *
              MvPowerSeries.subst (fun j => powerSeriesInVariable ℂ j (φ (b j)))
                (MvPowerSeries.map (σ := (Fin (m * h))) (algebraMap ℚ ℂ)
                  (MvPowerSeries.subst
                    (fun j => (MvPowerSeries.X (π.symm j) : MvPowerSeries (Fin (m * h)) ℚ))
                    (auxiliaryFormalSeries f h D ε t)))))‖ ≤
          Real.exp (Real.log ((auxiliaryFreeIndices m h D ε).card : ℝ) +
            S + (m * h : ℕ) * C +
            blockGridGrowth b (fun q => circleLogProfile (ψ q)) D ξ ε B +
            (M : ℝ) * (m * h : ℕ) * Real.log (m * h : ℕ)) := by
  have hcψ (q : κ) := (hdψ q).continuousOn
  obtain ⟨B, hB, hprofile⟩ := exists_bound_circleLogProfile ψ hcψ hne
  obtain ⟨C, hclear⟩ := exists_cleared_family_boundary_bound
    (fun iq : Fin m × κ => P iq.1 iq.2) (fun _ : Unit => id) H
    (fun iq _ => (hH iq.1 iq.2).continuousOn)
  refine ⟨B, hB, C, ?_⟩
  intro ξ ρ hξ hρ
  obtain ⟨η, hη, hweighted⟩ := exists_auxiliary_block_weighted_growth_bound ψ hcψ hne hξ
  obtain ⟨c, hc, N, hN⟩ := exists_damped_seeded_auxiliary_growth_bound (κ := κ) hη hρ
  refine ⟨c, hc, N + 1, ?_⟩
  intro h D ε hd hD hε b hsize t π S ht
  have hd0 : 0 < m * h := lt_of_lt_of_le (Nat.zero_lt_succ N) hd
  have hlog (θ : Fin (m * h) → AddCircle (2 * Real.pi)) (j : Fin (m * h)) :
      Real.log ‖ψ (b j) (fourier 1 (θ j))‖ ≤ B := by
    rw [← circleLogProfile_torusUnitRepresentative]
    exact (le_abs_self _).trans (hprofile _ _
      ⟨(torusUnitRepresentative_mem_Ico _).1, (torusUnitRepresentative_mem_Ico _).2.le⟩)
  obtain ⟨M, hM, hupper, hW, hcoeff⟩ :=
    hN m h D ε (Nat.le_of_succ_le hd) b hsize f F t π
      (fun j => φ (b j)) (fun j => ψ (b j)) (fun i j => P i (b j)) H hf
      (fun j => hψ (b j)) (fun j => hφ (b j)) (fun i j => hP i (b j))
      (fun j => hdψ (b j))
      (fun i j => hH i (b j)) S C B
      (blockGridGrowth b (fun q => circleLogProfile (ψ q)) D ξ ε B) hB ht
      (fun θ i j => hclear (i, b j) () (θ j)) hlog
      (fun θ hgood v => hweighted m h D ε hD b θ hgood B hprofile π v)
  exact ⟨M, hM, damped_exponent_le_of_blockGridGrowth b
    (fun q => circleLogProfile (ψ q)) hd0 hc (Nat.cast_nonneg D) hξ.le hε hB
    hprofile hupper, hW, hcoeff⟩

end DirichletL

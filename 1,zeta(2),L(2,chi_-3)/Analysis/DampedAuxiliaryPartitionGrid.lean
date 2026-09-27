import Analysis.DampedAuxiliaryFamilyGrid
import Analysis.PartitionBlocks

/-!
The finite coefficient bound for the paper's actual consecutive blocks,
CDT v2 TeX 3998-4028 and 4069-4228, and published UDC equations
2.5.15-2.5.24. The literal series and parameter order are recorded before

The continuation interface is recorded before this revision in
-/

namespace DirichletL

open scoped Classical Topology

theorem exists_damped_auxiliary_partition_grid_bound {s m : ℕ} (hs : 0 < s)
    (a : Fin (s + 1) → ℝ) (ha : StrictMono a)
    (ha0 : a 0 = 0) (ha1 : a (Fin.last s) = 1)
    (f : Fin m → PowerSeries ℚ) (F : Fin m → ℂ → ℂ)
    (φ : Fin s → PowerSeries ℂ) (ψ : Fin s → ℂ → ℂ)
    (P : Fin m → Fin s → ℂ → ℂ) (H : Polynomial ℂ)
    (hf : ∀ i, HasFPowerSeriesAt (F i) (complexSeries (f i)) 0)
    (hψ : ∀ q, HasFPowerSeriesAt (ψ q)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n (φ q))) 0)
    (hφ : ∀ q, PowerSeries.constantCoeff (R := ℂ) (φ q) = 0)
    (hP : ∀ i q, P i q =ᶠ[𝓝 (0 : ℂ)] fun z => F i (ψ q z))
    (hdψ : ∀ q, AnalyticOnNhd ℂ (ψ q) (Metric.closedBall 0 1))
    (hH : ∀ i q, AnalyticOnNhd ℂ (fun z => H.eval z * P i q z)
      (Metric.closedBall 0 1))
    (hne : ∀ q (z : ℂ), ‖z‖ = 1 → ψ q z ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, ∀ ξ : ℝ, 0 < ξ →
      ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ h : ℕ, N ≤ m * h →
      ∃ b : Fin (m * h) → Fin s,
        (∀ j q, b j = q ↔ a q.castSucc * (m * h : ℕ) ≤ (j.val : ℝ) + 1 ∧
          ((j.val : ℝ) + 1 < a q.succ * (m * h : ℕ) ∨ q.succ = Fin.last s)) ∧
        (∀ q, |((Finset.univ.filter (fun j => b j = q)).card : ℝ) -
          (a q.succ - a q.castSucc) * (m * h : ℕ)| ≤ 1) ∧
        ∀ (D : ℕ) (ε : ℝ), 0 < D → 0 ≤ ε →
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
  obtain ⟨ρ, hρ, Np, hNp⟩ := exists_partition_block_proportions hs a ha ha0 ha1
  obtain ⟨B, hB, C, hfamily⟩ :=
    exists_damped_auxiliary_family_grid_bound f F φ ψ P H hf hψ hφ hP hdψ hH hne
  refine ⟨B, hB, C, ?_⟩
  intro ξ hξ
  obtain ⟨c, hc, Na, hNa⟩ := hfamily ξ ρ hξ hρ
  refine ⟨c, hc, max Np Na, ?_⟩
  intro h hd
  obtain ⟨b, hb, hcard, hsize⟩ := hNp (m * h) ((le_max_left Np Na).trans hd)
  refine ⟨b, hb, hcard, ?_⟩
  intro D ε hD hε t π S ht
  exact hNa h D ε ((le_max_right Np Na).trans hd) hD hε b hsize t π S ht

end DirichletL

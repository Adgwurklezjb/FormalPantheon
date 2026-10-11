import Analysis.DampedAuxiliaryCauchy
import Analysis.SeededAuxiliaryNorm

/-!
The actual auxiliary growth bound in CDT v2, supplied TeX 4130-4150
and 4190-4228, and published UDC equations 2.5.15-2.5.24. Meanings,
the uniform choice of exponent, and the remaining weighted-growth

The continuation interface is recorded before this revision in
-/

namespace DirichletL

open scoped Classical Topology

theorem exists_damped_seeded_auxiliary_growth_bound {κ : Type*}
    [Fintype κ] [DecidableEq κ] {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ (m h D : ℕ) (ε : ℝ), N ≤ m * h →
      ∀ b : Fin (m * h) → κ,
      (∀ k, ρ * (m * h : ℕ) ≤ ((Finset.univ.filter (fun j => b j = k)).card : ℝ)) →
      ∀ (f : Fin m → PowerSeries ℚ) (F : Fin m → ℂ → ℂ)
        (t : ↥(auxiliaryFreeIndices m h D ε) → ℤ) (π : Equiv.Perm (Fin (m * h)))
        (φ : Fin (m * h) → PowerSeries ℂ) (ψ : Fin (m * h) → ℂ → ℂ)
        (P : Fin m → Fin (m * h) → ℂ → ℂ) (H : Polynomial ℂ),
      (∀ i, HasFPowerSeriesAt (F i) (complexSeries (f i)) 0) →
      (∀ j, HasFPowerSeriesAt (ψ j)
        (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n (φ j))) 0) →
      (∀ j, PowerSeries.constantCoeff (R := ℂ) (φ j) = 0) →
      (∀ i j, P i j =ᶠ[𝓝 (0 : ℂ)] fun z => F i (ψ j z)) →
      (∀ j, AnalyticOnNhd ℂ (ψ j) (Metric.closedBall 0 1)) →
      (∀ i j, AnalyticOnNhd ℂ (fun z => H.eval z * P i j z) (Metric.closedBall 0 1)) →
      ∀ S C L Γ : ℝ, 0 ≤ L →
      (∀ v, ‖(t v : ℂ)‖ ≤ Real.exp S) →
      (∀ (θ : Fin (m * h) → AddCircle (2 * Real.pi)) i j,
        ‖H.eval (fourier 1 (θ j)) * P i j (fourier 1 (θ j))‖ ≤ Real.exp C) →
      (∀ (θ : Fin (m * h) → AddCircle (2 * Real.pi)) j,
        Real.log ‖ψ j (fourier 1 (θ j))‖ ≤ L) →
      (∀ θ : Fin (m * h) → AddCircle (2 * Real.pi),
        (∀ k, HasIntervalDiscrepancyLE
          (fun i => torusUnitRepresentative
            (θ ((Finset.univ.filter (fun j => b j = k)).orderEmbOfFin rfl i))) η) →
        ∀ v : ↥(auxiliaryFreeIndices m h D ε),
          ∑ j, ((v.val.2 (π j)).val : ℝ) * Real.log ‖ψ j (fourier 1 (θ j))‖ ≤ Γ) →
      ∃ M : ℕ, 0 < M ∧
        (M : ℝ) ≤ max 0 ((m * h : ℕ) * (D : ℝ) * L - Γ) /
          (c * (m * h : ℕ) ^ 2) + 2 ∧
        blockVandermondePolynomial (R := ℂ) b M ≠ 0 ∧
        ∀ n : Fin (m * h) →₀ ℕ,
        ‖MvPowerSeries.coeff (R := ℂ) n
          ((blockVandermondePolynomial (R := ℂ) b M : MvPowerSeries (Fin (m * h)) ℂ) *
            ((∏ j, powerSeriesInVariable ℂ j (H : PowerSeries ℂ)) *
              MvPowerSeries.subst (fun j => powerSeriesInVariable ℂ j (φ j))
                (MvPowerSeries.map (σ := (Fin (m * h))) (algebraMap ℚ ℂ)
                  (MvPowerSeries.subst
                    (fun j => (MvPowerSeries.X (π.symm j) : MvPowerSeries (Fin (m * h)) ℚ))
                    (auxiliaryFormalSeries f h D ε t)))))‖ ≤
          Real.exp (Real.log ((auxiliaryFreeIndices m h D ε).card : ℝ) +
            S + (m * h : ℕ) * C + Γ + (M : ℝ) * (m * h : ℕ) * Real.log (m * h : ℕ)) := by
  obtain ⟨c, hc, N, hN⟩ := exists_damped_seeded_auxiliary_cauchy_bound (κ := κ) hη hρ
  refine ⟨c, hc, N, ?_⟩
  intro m h D ε hd b hsize f F t π φ ψ P H hf hψ hφ hP hdψ hH S C L Γ hL ht hclear hlog hweight
  let E := Real.log ((auxiliaryFreeIndices m h D ε).card : ℝ) + S + (m * h : ℕ) * C
  obtain ⟨M, hM, hupper, hW, hcoeff⟩ :=
    hN m h D ε hd b hsize f F t π φ ψ P H hf hψ hφ hP hdψ hH
      (E + Γ) (E + (m * h : ℕ) * (D : ℝ) * L)
      (fun θ => norm_seeded_auxiliary_sum_le_of_log_bound h D ε t π ψ P H
        (fun j => fourier 1 (θ j)) S C L hL ht (hclear θ) (hlog θ))
      (fun θ hgood => norm_seeded_auxiliary_sum_le h D ε t π ψ P H
        (fun j => fourier 1 (θ j)) S C Γ ht (hclear θ) (hweight θ hgood))
  refine ⟨M, hM, ?_, hW, hcoeff⟩
  have hgap : (E + (m * h : ℕ) * (D : ℝ) * L) - (E + Γ) =
      (m * h : ℕ) * (D : ℝ) * L - Γ := by ring
  simpa only [hgap] using hupper

end DirichletL

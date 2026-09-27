import Analysis.BlockVandermondeCoefficient
import Analysis.DampedTorusBound
import Analysis.SeededAuxiliaryCauchy

/-!
The actual damped auxiliary coefficient in CDT v2, supplied TeX 4092-4137
and 4200-4228, and published UDC Sections 2.5.14-2.5.25. The quantifier
order and retained analytic hypotheses precede this proof in

The continuation interface is recorded before this revision in
-/

namespace DirichletL

open scoped Classical Topology

theorem exists_damped_seeded_auxiliary_cauchy_bound {κ : Type*}
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
      ∀ A B : ℝ,
      (∀ θ : Fin (m * h) → AddCircle (2 * Real.pi),
        ‖∑ v, (t v : ℂ) * ∏ j, H.eval (fourier 1 (θ j)) *
          ψ j (fourier 1 (θ j)) ^ (v.val.2 (π j)).val *
            P (v.val.1 (π j)) j (fourier 1 (θ j))‖ ≤ Real.exp B) →
      (∀ θ : Fin (m * h) → AddCircle (2 * Real.pi),
        (∀ k, HasIntervalDiscrepancyLE
          (fun i => torusUnitRepresentative
            (θ ((Finset.univ.filter (fun j => b j = k)).orderEmbOfFin rfl i))) η) →
        ‖∑ v, (t v : ℂ) * ∏ j, H.eval (fourier 1 (θ j)) *
          ψ j (fourier 1 (θ j)) ^ (v.val.2 (π j)).val *
            P (v.val.1 (π j)) j (fourier 1 (θ j))‖ ≤ Real.exp A) →
      ∃ M : ℕ, 0 < M ∧
        (M : ℝ) ≤ max 0 (B - A) / (c * (m * h : ℕ) ^ 2) + 2 ∧
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
          Real.exp (A + (M : ℝ) * (m * h : ℕ) * Real.log (m * h : ℕ)) := by
  obtain ⟨c, hc, N, hN⟩ := exists_block_damped_torus_bound (κ := κ) hη hρ
  refine ⟨c, hc, N, ?_⟩
  intro m h D ε hd b hsize f F t π φ ψ P H hf hψ hφ hP hdψ hH A B hglobal hgood
  let G : (Fin (m * h) → AddCircle (2 * Real.pi)) → ℂ := fun θ =>
    ∑ v, (t v : ℂ) * ∏ j, H.eval (fourier 1 (θ j)) *
      ψ j (fourier 1 (θ j)) ^ (v.val.2 (π j)).val *
        P (v.val.1 (π j)) j (fourier 1 (θ j))
  obtain ⟨M, hM, hupper, hbound⟩ := hN (m * h) hd b hsize G A B hglobal hgood
  refine ⟨M, hM, hupper, blockVandermondePolynomial_ne_zero b M, ?_⟩
  intro n
  exact norm_coeff_seeded_auxiliaryFormalSeries_le_of_bound f F h D ε t π φ ψ P H
    (blockVandermondePolynomial b M) hf hψ hφ hP hdψ hH n
    (Real.exp (A + (M : ℝ) * (m * h : ℕ) * Real.log (m * h : ℕ))) hbound

end DirichletL

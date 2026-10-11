import Analysis.DiscrepancyFourierWitness
import Analysis.FourierModeDamping

/-!
Deterministic Vandermonde damping from interval discrepancy in CDT v2,
supplied TeX 4054-4067, and published UDC Lemma 2.5.9. The finite-mode
implementation and exceptional cases are independently checked before
-/

namespace DirichletL

attribute [local instance] fact_one_pos

theorem exists_vandermonde_damping_of_interval_discrepancy {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∀ t : Fin d → ℝ,
      (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) → ¬HasIntervalDiscrepancyLE t ε →
      ‖(Matrix.vandermonde (fun i => fourier 1 (t i : AddCircle (1 : ℝ)))).det‖ <
        Real.exp (-c * (d : ℝ) ^ 2) := by
  obtain ⟨K, hK, a, ha, hwitness⟩ :=
    exists_bounded_fourier_mode_of_not_hasIntervalDiscrepancyLE hε
  obtain ⟨c, hc, N, hN⟩ := exists_vandermonde_damping_of_fourier_mode hK ha
  refine ⟨c, hc, N + 1, ?_⟩
  intro d hd t hcube hbad
  obtain ⟨m, hm, hmK, hmode⟩ := hwitness d (by omega) t hcube hbad
  exact hN d (by omega) (fun i => fourier 1 (t i : AddCircle (1 : ℝ)))
    (fun i => Circle.norm_coe _) ⟨m, hm, hmK, hmode.le⟩

end DirichletL

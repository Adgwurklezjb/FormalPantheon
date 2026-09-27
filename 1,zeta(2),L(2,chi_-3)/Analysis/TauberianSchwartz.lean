import Analysis.TauberianBoundary
import Analysis.TauberianApproximation

/-!
The Fourier boundary limit for arbitrary Schwartz functions, on the
Wiener-Ikehara route to CDT v2 Section 2.2 (supplied TeX 3291-3310).
Based on the PrimeNumberTheoremAnd contributors, Wiener.lean at revision
0766218b21b11ddf24103352ece7f0cb730945e0, lines 1545-1636, archived with
-/

namespace DirichletL

open MeasureTheory Filter Set
open scoped Topology FourierTransform SchwartzMap

theorem tauberian_residual_sub {f : ℕ → ℂ} {C : ℝ}
    (hsum : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ C * n) {x : ℝ} (hx : 0 < x)
    (ψ φ : 𝓢(ℝ, ℂ)) (A : ℂ) :
    (∑' n, tauberianFourierTerm f (ψ - φ) x n) -
        A * (∫ u in Ici (-Real.log x), 𝓕 (ψ - φ) (u / (2 * Real.pi))) =
      ((∑' n, tauberianFourierTerm f ψ x n) -
        A * (∫ u in Ici (-Real.log x), 𝓕 ψ (u / (2 * Real.pi)))) -
      ((∑' n, tauberianFourierTerm f φ x n) -
        A * (∫ u in Ici (-Real.log x), 𝓕 φ (u / (2 * Real.pi)))) := by
  have hF (u : ℝ) : 𝓕 (ψ - φ) u = 𝓕 ψ u - 𝓕 φ u := by
    change SchwartzMap.fourierTransformCLM ℂ (ψ - φ) u = _
    rw [map_sub]
    rfl
  have hs : (∑' n, tauberianFourierTerm f (ψ - φ) x n) =
      (∑' n, tauberianFourierTerm f ψ x n) - (∑' n, tauberianFourierTerm f φ x n) := by
    simp only [tauberianFourierTerm, hF, mul_sub]
    exact (summable_norm_tauberianFourierTerm hsum hx ψ).of_norm.tsum_sub
      (summable_norm_tauberianFourierTerm hsum hx φ).of_norm
  rw [hs]
  simp only [hF]
  have hi (χ : 𝓢(ℝ, ℂ)) :
      IntegrableOn (fun u : ℝ => 𝓕 χ (u / (2 * Real.pi))) (Ici (-Real.log x)) :=
    ((SchwartzMap.fourierTransformCLM ℂ χ).integrable.comp_div (by positivity)).integrableOn
  rw [integral_sub (hi ψ) (hi φ)]
  ring

theorem tendsto_tauberian_residual {f : ℕ → ℂ} {C : ℝ} {A : ℂ} {G : ℂ → ℂ}
    (hsum : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ C * n)
    (hf : ∀ σ : ℝ, 1 < σ → LSeriesSummable f (σ : ℂ))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : EqOn G (fun s => LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (ψ : 𝓢(ℝ, ℂ)) :
    Tendsto (fun x : ℝ => (∑' n, tauberianFourierTerm f ψ x n) -
      A * (∫ u in Ici (-Real.log x), 𝓕 ψ (u / (2 * Real.pi)))) atTop (𝓝 0) := by
  let R (φ : 𝓢(ℝ, ℂ)) (x : ℝ) := (∑' n, tauberianFourierTerm f φ x n) -
    A * (∫ u in Ici (-Real.log x), 𝓕 φ (u / (2 * Real.pi)))
  change Tendsto (R ψ) atTop (𝓝 0)
  have hC : 0 ≤ C := by
    have h : ‖f 0‖ ≤ C := by simpa using hsum 1
    exact (norm_nonneg _).trans h
  let M := C * (1 + 2 * Real.pi ^ 2) + ‖A‖ * (2 * Real.pi ^ 2)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨φ, hφ, hsmall⟩ := exists_hasCompactSupport_tauberianFourierSize_sub_lt ψ
    (show 0 < (ε / 2) / (1 + M) by positivity)
  have hlim : Tendsto (R φ) atTop (𝓝 0) :=
    tendsto_tauberian_residual_of_hasCompactSupport hsum hf hG hG' φ hφ
  have he := (Metric.tendsto_nhds.mp hlim) (ε / 2) (by positivity)
  filter_upwards [eventually_ge_atTop (1 : ℝ), he] with x hx hlimx
  have hx' := zero_lt_one.trans_le hx
  have hb : ‖R (ψ - φ) x‖ < ε / 2 := by
    calc
      _ ≤ tauberianFourierSize (ψ - φ) * M := norm_tauberian_residual_le hsum hx' (ψ - φ) A
      _ ≤ tauberianFourierSize (ψ - φ) * (1 + M) :=
        mul_le_mul_of_nonneg_left (by linarith) (tauberianFourierSize_nonneg _)
      _ < (ε / 2) / (1 + M) * (1 + M) :=
        mul_lt_mul_of_pos_right hsmall (by positivity)
      _ = ε / 2 := div_mul_cancel₀ _ (by positivity)
  have hsub : R (ψ - φ) x = R ψ x - R φ x := tauberian_residual_sub hsum hx' ψ φ A
  calc
    dist (R ψ x) 0 = ‖R (ψ - φ) x + R φ x‖ := by rw [hsub, sub_add_cancel, dist_zero_right]
    _ ≤ ‖R (ψ - φ) x‖ + ‖R φ x‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hb (by simpa only [dist_zero_right] using hlimx)
    _ = ε := add_halves ε

theorem tendsto_tsum_tauberianFourierTerm {f : ℕ → ℂ} {C : ℝ} {A : ℂ} {G : ℂ → ℂ}
    (hsum : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ C * n)
    (hf : ∀ σ : ℝ, 1 < σ → LSeriesSummable f (σ : ℂ))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : EqOn G (fun s => LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (ψ : 𝓢(ℝ, ℂ)) :
    Tendsto (fun x : ℝ => ∑' n, tauberianFourierTerm f ψ x n) atTop
      (𝓝 (A * ∫ u : ℝ, 𝓕 ψ (u / (2 * Real.pi)))) := by
  have hi : Integrable (fun u : ℝ => 𝓕 ψ (u / (2 * Real.pi))) :=
    (SchwartzMap.fourierTransformCLM ℂ ψ).integrable.comp_div (by positivity)
  have ht := (aecover_Ici (tendsto_neg_atBot_iff.mpr
    Real.tendsto_log_atTop)).integral_tendsto_of_countably_generated hi
  simpa only [sub_add_cancel, zero_add] using
    (tendsto_tauberian_residual hsum hf hG hG' ψ).add (ht.const_mul A)

end DirichletL

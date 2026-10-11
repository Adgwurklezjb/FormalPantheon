import Analysis.ZagierConjugateBasis
import Analysis.ZagierSummandTransport
import Analysis.ZagierEndpointLoop

/-!
Trivial conjugate transport near ordinary points, for CDT v2, `14functions`.
The fourth-order projected paths still avoid every singular image value.
-/

namespace DirichletL

open Filter Set unitInterval
open scoped Topology

theorem exists_zagierConjugate_trivial_transport_ball {z0 : ℂ}
    (hz0 : z0 * (z0 - 1) ^ 2 * (8 * z0 + 1) ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ (b : zagierODERegularSet) {x : ℂ} (δ : Path x x),
      (∀ t, δ t ∈ Metric.ball z0 R) → ∀ (h₁ : ∀ t, δ t ≠ 1)
      (hreg : ∀ t, mobiusCoordinate (δ t) ∈ zagierODERegularSet) (hx : x ≠ 1)
      (φ : zagierSolutionGerms (mobiusCoordinate x)), φ ∈ zagierConjugateSummand hx →
        zagierPathTransport b (zagierMobiusPath δ h₁ hreg) φ = φ := by
  obtain ⟨R, hR, g, h, hgh⟩ := exists_zagierConjugate_local_basis hz0
  refine ⟨R, hR, ?_⟩
  intro b x δ hδ h₁ hreg hx φ hφ
  have hxball : x ∈ Metric.ball z0 R := by simpa only [Path.source] using hδ 0
  obtain ⟨f, hf, hfo, hφf⟩ := hφ
  obtain ⟨a, c, he⟩ := (hgh x hxball).2.2.2.2.2 f hf hfo
  have hF (t : I) : AnalyticAt ℂ (fun w => a * g w + c * h w) (δ t) :=
    ((hgh (δ t) (hδ t)).1.const_smul (c := a)).add
      ((hgh (δ t) (hδ t)).2.1.const_smul (c := c))
  have hφF : mobiusGermPullback hx (φ : Germ (𝓝 (mobiusCoordinate x)) ℂ) =
      (fun w => a * g w + c * h w : ℂ → ℂ) := hφf.trans (Germ.coe_eq.mpr he)
  have ht := mobiusGermPullback_zagierPathTransport_of_analyticContinuation b δ h₁ hreg hx hx
    (AnalyticContinuationAlong.const δ.continuous hF) φ hφF
  have hxreg : mobiusCoordinate x ∈ zagierODERegularSet := by
    simpa only [Path.source] using hreg 0
  obtain ⟨hx₀, hx₂⟩ := mobiusCoordinate_regular_ne_zero_two hxreg
  apply Subtype.ext
  exact mobiusGermPullback_injective hx₀ hx hx₂ (ht.trans hφF.symm)

theorem exists_zagierEndpointCircle_radius_subset_ball {R : ℝ} (hR : 0 < R) :
    ∃ S : ℝ, 0 < S ∧ ∀ r : ℝ, ∀ hr : r ∈ Ioo 0 (1 / 9 : ℝ), r < S →
      ∀ t : I, zagierEndpointCirclePath r hr t ∈ Metric.ball (1 / 9 : ℂ) R := by
  have hT : Tendsto zagierEndpointCoordinate (𝓝 (0 : ℂ)) (𝓝 (1 / 9 : ℂ)) := by
    simpa only [zagierEndpointCoordinate_zero, one_div] using
      (analyticAt_zagierEndpointCoordinate (by norm_num : (0 : ℂ) ≠ 1)).continuousAt.tendsto
  obtain ⟨S, hS, hball⟩ := Metric.mem_nhds_iff.mp
    (hT.eventually (Metric.ball_mem_nhds (1 / 9 : ℂ) hR))
  refine ⟨S, hS, ?_⟩
  intro r hr hrS t
  apply hball
  simpa only [Metric.mem_ball, dist_zero_right, norm_complexCirclePath,
    abs_of_pos hr.1] using hrS

end DirichletL

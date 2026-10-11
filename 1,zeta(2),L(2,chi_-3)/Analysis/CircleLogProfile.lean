import Analysis.TorusBlockDamping

/-!
Fixed circle profiles and family constants for CDT v2, supplied TeX 4130-4228.
Continuity, boundary nonvanishing, and quantifier checks precede these bodies
-/

namespace DirichletL

/-- The real logarithmic norm of a map evaluated on the circle with period-one coordinates. -/
noncomputable def circleLogProfile (ψ : ℂ → ℂ) (u : ℝ) : ℝ :=
  Real.log ‖ψ (fourier 1 (u : AddCircle (1 : ℝ)))‖

theorem continuous_circleLogProfile {ψ : ℂ → ℂ}
    (hψ : ContinuousOn ψ (Metric.closedBall 0 1))
    (hne : ∀ z : ℂ, ‖z‖ = 1 → ψ z ≠ 0) : Continuous (circleLogProfile ψ) := by
  have hc : Continuous (fun u : ℝ => ψ (fourier 1 (u : AddCircle (1 : ℝ)))) := by
    apply hψ.comp_continuous ((fourier 1).continuous.comp (AddCircle.continuous_mk' 1))
    intro u
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq (Circle.norm_coe _)
  exact hc.norm.log (fun u => norm_ne_zero_iff.mpr (hne _ (Circle.norm_coe _)))

theorem circleLogProfile_torusUnitRepresentative (ψ : ℂ → ℂ)
    (θ : AddCircle (2 * Real.pi)) :
    circleLogProfile ψ (torusUnitRepresentative θ) = Real.log ‖ψ (fourier 1 θ)‖ := by
  rw [circleLogProfile, fourier_torusUnitRepresentative]

theorem exists_bound_circleLogProfile {κ : Type*} [Fintype κ]
    (ψ : κ → ℂ → ℂ) (hψ : ∀ q, ContinuousOn (ψ q) (Metric.closedBall 0 1))
    (hne : ∀ q (z : ℂ), ‖z‖ = 1 → ψ q z ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q u, u ∈ Set.Icc (0 : ℝ) 1 → |circleLogProfile (ψ q) u| ≤ B := by
  have hc : ContinuousOn (fun u q => circleLogProfile (ψ q) u) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_pi.mpr (fun q => (continuous_circleLogProfile (hψ q) (hne q)).continuousOn)
  obtain ⟨U, hU⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max 0 U, le_max_left _ _, ?_⟩
  intro q u hu
  exact (norm_le_pi_norm (fun q => circleLogProfile (ψ q) u) q).trans
    ((hU u hu).trans (le_max_right _ _))

theorem exists_cleared_family_boundary_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : ι → ℂ → ℂ) (ψ : κ → ℂ → ℂ) (H : Polynomial ℂ)
    (hclear : ∀ i q, ContinuousOn (fun z => H.eval z * F i (ψ q z))
      (Metric.closedBall 0 1)) :
    ∃ C : ℝ, ∀ i q (θ : AddCircle (2 * Real.pi)),
      ‖H.eval (fourier 1 θ) * F i (ψ q (fourier 1 θ))‖ ≤ Real.exp C := by
  have hc : ContinuousOn (fun z (iq : ι × κ) => H.eval z * F iq.1 (ψ iq.2 z))
      (Metric.closedBall 0 1) := continuousOn_pi.mpr (fun iq => hclear iq.1 iq.2)
  obtain ⟨U, hU⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hc
  refine ⟨Real.log (max 1 U), ?_⟩
  intro i q θ
  rw [Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
  apply (norm_le_pi_norm (fun iq : ι × κ =>
    H.eval (fourier 1 θ) * F iq.1 (ψ iq.2 (fourier 1 θ))) (i, q)).trans
  apply (hU _ ?_).trans (le_max_right _ _)
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_eq (Circle.norm_coe _)

end DirichletL

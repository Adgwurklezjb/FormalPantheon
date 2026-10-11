import Analysis.PairwiseMaximumSymmetry
import Analysis.HolonomyBoundaryBound

/-!
The two-radius specialization in CDT v2, supplied TeX 8325-8333 and 8384-8404.
-/

namespace DirichletL

open scoped Topology

/-- The signed maximum integral for the inner/outer mixture with masses p and 1-p. -/
noncomputable def twoRadiusMaxIntegral (ψ : ℂ → ℂ) (r p : ℝ) : ℝ :=
  p ^ 2 * pairwiseMaxIntegral
    (circleLogProfile (fun z => ψ ((r : ℂ) * z)))
    (circleLogProfile (fun z => ψ ((r : ℂ) * z))) +
  2 * p * (1 - p) * pairwiseMaxIntegral
    (circleLogProfile (fun z => ψ ((r : ℂ) * z))) (circleLogProfile ψ) +
  (1 - p) ^ 2 * pairwiseMaxIntegral (circleLogProfile ψ) (circleLogProfile ψ)

theorem cdt_two_radius_holonomy_bound (a₀ b₀ c₀ : ℤ)
    (hrel : (a₀ : ℝ) + (b₀ : ℝ) * (lTwoChiMinusThree / 2) +
      (c₀ : ℝ) * (zetaTwo / 4) = 0) (hne : ¬(a₀ = 0 ∧ b₀ = 0 ∧ c₀ = 0))
    (ψ : ℂ → ℂ) (P : Fin 14 → ℂ → ℂ) (hψ0 : ψ 0 = 0)
    (hP : ∀ i, P i =ᶠ[𝓝 (0 : ℂ)] fun z => cdtHolonomyFamily a₀ b₀ c₀ i (ψ z))
    (hderiv : deriv ψ 0 ≠ 0) (hdψ : AnalyticOnNhd ℂ ψ (Metric.closedBall 0 1))
    (hmero : ∀ i, MeromorphicOn (P i) (Metric.ball 0 1))
    {r p : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hp : 0 < p) (hp1 : p < 1) :
    14 * (Real.log ‖deriv ψ 0‖ + p ^ 2 * Real.log r) ≤
      14 * (16603 / 3920 : ℝ) + twoRadiusMaxIntegral ψ r p := by
  let v : Fin 3 → ℝ := ![0, p, 1]
  let Ψ : Fin 2 → ℂ → ℂ := ![fun z => ψ ((r : ℂ) * z), ψ]
  let Q (i : Fin 14) : Fin 2 → ℂ → ℂ := ![fun z => P i ((r : ℂ) * z), P i]
  have hv : StrictMono v := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    · exact hp
    · exact hp1
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hscale : Filter.Tendsto (fun z : ℂ => (r : ℂ) * z)
      (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa only [id_eq, mul_zero] using
      ((continuous_const.mul continuous_id).tendsto (0 : ℂ) :
        Filter.Tendsto (fun z : ℂ => (r : ℂ) * z) (𝓝 0) (𝓝 ((r : ℂ) * 0)))
  have hdinner : AnalyticOnNhd ℂ (fun z => ψ ((r : ℂ) * z)) (Metric.closedBall 0 1) := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have hscaled : (r : ℂ) * z ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_left hz1 hr.le).trans (by simpa only [mul_one] using hr1)
    exact (hdψ _ hscaled).comp' (analyticAt_const.mul analyticAt_id)
  have hdi : deriv (fun z => ψ ((r : ℂ) * z)) 0 = (r : ℂ) * deriv ψ 0 := by
    have hg : HasDerivAt ψ (deriv ψ 0) ((r : ℂ) * 0) := by
      simpa only [mul_zero] using (hdψ 0 (by simp)).differentiableAt.hasDerivAt
    have hc : HasDerivAt (fun z : ℂ => (r : ℂ) * z) (r : ℂ) 0 := by
      simpa only [mul_one] using (hasDerivAt_id (𝕜 := ℂ) 0).const_mul (r : ℂ)
    simpa only [Function.comp_def, mul_comm] using (hg.comp 0 hc).deriv
  have hΨ0 : ∀ q, Ψ q 0 = 0 := by
    intro q
    fin_cases q <;> simp [Ψ, hψ0]
  have hQ : ∀ i q, Q i q =ᶠ[𝓝 (0 : ℂ)] fun z =>
      cdtHolonomyFamily a₀ b₀ c₀ i (Ψ q z) := by
    intro i q
    fin_cases q
    · exact (hP i).comp_tendsto hscale
    · exact hP i
  have hdΨ : ∀ q, AnalyticOnNhd ℂ (Ψ q) (Metric.closedBall 0 1) := by
    intro q
    fin_cases q
    · exact hdinner
    · exact hdψ
  have hΨderiv : ∀ q, deriv (Ψ q) 0 ≠ 0 := by
    intro q
    fin_cases q
    · change deriv (fun z => ψ ((r : ℂ) * z)) 0 ≠ 0
      rw [hdi]
      exact mul_ne_zero hrC hderiv
    · exact hderiv
  have hQmero : ∀ i q, MeromorphicOn (Q i q) (Metric.ball 0 1) := by
    intro i q
    fin_cases q
    · intro z hz
      apply meromorphicAt_comp_const_mul hrC
      apply hmero i
      have hz1 : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
      rw [Metric.mem_ball, dist_zero_right, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_right hr1 (norm_nonneg z)).trans_lt
        (by simpa only [one_mul] using hz1)
    · exact hmero i
  have hb := cdt_partition_holonomy_bound_meromorphic_openDisc a₀ b₀ c₀ hrel hne
    (s := 2) (by norm_num) v hv (by rfl) (by rfl) Ψ Q hΨ0 hQ hΨderiv hdΨ hQmero
  have hlog : Real.log ‖deriv (fun z => ψ ((r : ℂ) * z)) 0‖ =
      Real.log r + Real.log ‖deriv ψ 0‖ := by
    rw [hdi, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Real.log_mul hr.ne' (norm_ne_zero_iff.mpr hderiv)]
  have hcomm := pairwiseMaxIntegral_comm (intervalIntegrable_circleLogProfile hdinner)
    (intervalIntegrable_circleLogProfile hdψ)
  simp [v, Ψ, Fin.sum_univ_two] at hb
  rw [hlog, ← hcomm] at hb
  convert hb using 1 <;> dsimp only [twoRadiusMaxIntegral] <;> ring

end DirichletL

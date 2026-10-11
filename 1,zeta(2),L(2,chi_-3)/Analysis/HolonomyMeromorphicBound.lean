import Analysis.HolonomyPartitionBound
import Analysis.AnalyticPowerSeries
import Analysis.ContinuedComposedFactors
import Analysis.MeromorphicDilation

/-!
Compact pole clearing and inner dilation for CDT v2 TeX 4008-4021, 4150-4153,

The continuation interface is recorded before this revision in
-/

namespace DirichletL

open scoped Classical Topology

theorem cdt_partition_holonomy_bound_of_meromorphic (a₀ b₀ c₀ : ℤ)
    (hrel : (a₀ : ℝ) + (b₀ : ℝ) * (lTwoChiMinusThree / 2) +
      (c₀ : ℝ) * (zetaTwo / 4) = 0) (hne : ¬(a₀ = 0 ∧ b₀ = 0 ∧ c₀ = 0))
    {s : ℕ} (hs : 0 < s) (v : Fin (s + 1) → ℝ) (hv : StrictMono v)
    (hv0 : v 0 = 0) (hv1 : v (Fin.last s) = 1) (ψ : Fin s → ℂ → ℂ)
    (P : Fin 14 → Fin s → ℂ → ℂ)
    (hψ0 : ∀ q, ψ q 0 = 0)
    (hP : ∀ i q, P i q =ᶠ[𝓝 (0 : ℂ)] fun z =>
      cdtHolonomyFamily a₀ b₀ c₀ i (ψ q z))
    (hderiv : ∀ q, deriv (ψ q) 0 ≠ 0)
    (hdψ : ∀ q, AnalyticOnNhd ℂ (ψ q) (Metric.closedBall 0 1))
    (hmero : ∀ i q, MeromorphicOn (P i q) (Metric.closedBall 0 1))
    (hcircle : ∀ q (z : ℂ), ‖z‖ = 1 → ψ q z ≠ 0) :
    14 * (∑ q, (v q.succ ^ 2 - v q.castSucc ^ 2) * Real.log ‖deriv (ψ q) 0‖) ≤
      14 * (16603 / 3920 : ℝ) + ∑ q : Fin s, ∑ r : Fin s,
        (v q.succ - v q.castSucc) * (v r.succ - v r.castSucc) *
        pairwiseMaxIntegral (circleLogProfile (ψ q)) (circleLogProfile (ψ r)) := by
  have hzero : (0 : ℂ) ∈ Metric.closedBall 0 1 := by simp
  choose φ hφ hφ0 _hφ1 using
    fun q => exists_powerSeries_of_analyticAt_zero (hdψ q 0 hzero)
  have hrelQ : ((a₀ : ℚ) : ℝ) + ((b₀ : ℚ) : ℝ) * (lTwoChiMinusThree / 2) +
      ((c₀ : ℚ) : ℝ) * (zetaTwo / 4) = 0 := by
    simpa only [Rat.cast_intCast] using hrel
  obtain ⟨H, hH0, hH⟩ := exists_common_polynomial_clear_continued_compact
    (cdtHolonomyFamily a₀ b₀ c₀) ψ P (isCompact_closedBall (0 : ℂ) 1)
    (fun i => (hasFPowerSeriesAt_cdtHolonomyFamily a₀ b₀ c₀ hrelQ i).analyticAt)
    (fun q => hdψ q 0 hzero) hψ0 hP hmero
  exact cdt_partition_holonomy_bound a₀ b₀ c₀ hrel hne hs v hv hv0 hv1 φ ψ P H hφ
    (fun q => (hφ0 q).trans (hψ0 q)) hP hderiv hdψ hH0 hH hcircle

theorem cdt_partition_holonomy_bound_inner_radius (a₀ b₀ c₀ : ℤ)
    (hrel : (a₀ : ℝ) + (b₀ : ℝ) * (lTwoChiMinusThree / 2) +
      (c₀ : ℝ) * (zetaTwo / 4) = 0) (hne : ¬(a₀ = 0 ∧ b₀ = 0 ∧ c₀ = 0))
    {s : ℕ} (hs : 0 < s) (v : Fin (s + 1) → ℝ) (hv : StrictMono v)
    (hv0 : v 0 = 0) (hv1 : v (Fin.last s) = 1) (ψ : Fin s → ℂ → ℂ)
    (P : Fin 14 → Fin s → ℂ → ℂ)
    (hψ0 : ∀ q, ψ q 0 = 0)
    (hP : ∀ i q, P i q =ᶠ[𝓝 (0 : ℂ)] fun z =>
      cdtHolonomyFamily a₀ b₀ c₀ i (ψ q z))
    (hderiv : ∀ q, deriv (ψ q) 0 ≠ 0)
    (hdψ : ∀ q, AnalyticOnNhd ℂ (ψ q) (Metric.closedBall 0 1))
    (hmero : ∀ i q, MeromorphicOn (P i q) (Metric.ball 0 1))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hcircle : ∀ q (z : ℂ), ‖z‖ = r → ψ q z ≠ 0) :
    14 * (∑ q, (v q.succ ^ 2 - v q.castSucc ^ 2) *
      Real.log ‖(r : ℂ) * deriv (ψ q) 0‖) ≤
      14 * (16603 / 3920 : ℝ) + ∑ q : Fin s, ∑ t : Fin s,
        (v q.succ - v q.castSucc) * (v t.succ - v t.castSucc) *
        pairwiseMaxIntegral (circleLogProfile (fun z => ψ q ((r : ℂ) * z)))
          (circleLogProfile (fun z => ψ t ((r : ℂ) * z))) := by
  let θ (q : Fin s) (z : ℂ) := ψ q ((r : ℂ) * z)
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hnorm (z : ℂ) : ‖(r : ℂ) * z‖ = r * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hmulball (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
      (r : ℂ) * z ∈ Metric.ball (0 : ℂ) 1 := by
    have hz1 : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    rw [Metric.mem_ball, dist_zero_right, hnorm]
    calc
      r * ‖z‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hz1 hr.le
      _ = r := mul_one r
      _ < 1 := hr1
  have hdθ (q : Fin s) : AnalyticOnNhd ℂ (θ q) (Metric.closedBall 0 1) := by
    intro z hz
    exact (hdψ q ((r : ℂ) * z) (Metric.ball_subset_closedBall (hmulball z hz))).comp'
      (analyticAt_const.mul analyticAt_id)
  have hθ0 (q : Fin s) : θ q 0 = 0 := by simp only [θ, mul_zero, hψ0]
  have hθderiv (q : Fin s) : deriv (θ q) 0 = (r : ℂ) * deriv (ψ q) 0 := by
    have hg : HasDerivAt (ψ q) (deriv (ψ q) 0) ((r : ℂ) * 0) := by
      simpa only [mul_zero] using (hdψ q 0 (by simp)).differentiableAt.hasDerivAt
    have hscale : HasDerivAt (fun z : ℂ => (r : ℂ) * z) (r : ℂ) 0 := by
      simpa only [mul_one] using (hasDerivAt_id (𝕜 := ℂ) 0).const_mul (r : ℂ)
    simpa only [θ, Function.comp_def, mul_comm] using (hg.comp 0 hscale).deriv
  have hθnonzero (q : Fin s) : deriv (θ q) 0 ≠ 0 := by
    rw [hθderiv q]
    exact mul_ne_zero hrC (hderiv q)
  have hmeroP (i : Fin 14) (q : Fin s) : MeromorphicOn
      (fun z => P i q ((r : ℂ) * z)) (Metric.closedBall 0 1) := by
    intro z hz
    exact meromorphicAt_comp_const_mul hrC (hmero i q ((r : ℂ) * z) (hmulball z hz))
  have hscale : Filter.Tendsto (fun z : ℂ => (r : ℂ) * z)
      (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa only [id_eq, mul_zero] using
      ((continuous_const.mul continuous_id).tendsto (0 : ℂ) :
        Filter.Tendsto (fun z : ℂ => (r : ℂ) * z) (𝓝 0) (𝓝 ((r : ℂ) * 0)))
  have hPθ (i : Fin 14) (q : Fin s) :
      (fun z => P i q ((r : ℂ) * z)) =ᶠ[𝓝 (0 : ℂ)]
        fun z => cdtHolonomyFamily a₀ b₀ c₀ i (θ q z) :=
    (hP i q).comp_tendsto hscale
  have hcircleθ (q : Fin s) (z : ℂ) (hz : ‖z‖ = 1) : θ q z ≠ 0 := by
    apply hcircle q ((r : ℂ) * z)
    rw [hnorm, hz, mul_one]
  have hbound := cdt_partition_holonomy_bound_of_meromorphic a₀ b₀ c₀ hrel hne
    hs v hv hv0 hv1 θ (fun i q z => P i q ((r : ℂ) * z))
    hθ0 hPθ hθnonzero hdθ hmeroP hcircleθ
  simpa only [hθderiv, θ] using hbound

end DirichletL

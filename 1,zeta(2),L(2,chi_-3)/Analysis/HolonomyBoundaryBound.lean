import Analysis.HolonomyInnerRadii
import Analysis.PairwiseMaximumL1
import Analysis.CircleLogRadialL1

/-!
The outer-radius signed bound from CDT v2 TeX 3505-3540 and 4150-4153.

The continuation interface is recorded before this revision in
-/

namespace DirichletL

open Filter
open scoped Topology

theorem cdt_partition_holonomy_bound_meromorphic_openDisc (a₀ b₀ c₀ : ℤ)
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
    (hmero : ∀ i q, MeromorphicOn (P i q) (Metric.ball 0 1)) :
    14 * (∑ q, (v q.succ ^ 2 - v q.castSucc ^ 2) * Real.log ‖deriv (ψ q) 0‖) ≤
      14 * (16603 / 3920 : ℝ) + ∑ q : Fin s, ∑ t : Fin s,
        (v q.succ - v q.castSucc) * (v t.succ - v t.castSucc) *
        pairwiseMaxIntegral (circleLogProfile (ψ q)) (circleLogProfile (ψ t)) := by
  let f (r : ℝ) (q : Fin s) : ℝ → ℝ := circleLogProfile (fun z => ψ q ((r : ℂ) * z))
  let f₀ (q : Fin s) : ℝ → ℝ := circleLogProfile (ψ q)
  have hbase (q : Fin s) : IntervalIntegrable (f₀ q) MeasureTheory.volume 0 1 :=
    intervalIntegrable_circleLogProfile (hdψ q)
  have hproper : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r ∧ r < 1 := by
    filter_upwards [(eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr hr1
    exact ⟨hr, hr1⟩
  have hint (q : Fin s) : ∀ᶠ r : ℝ in 𝓝[<] 1,
      IntervalIntegrable (f r q) MeasureTheory.volume 0 1 := by
    filter_upwards [hproper] with r hr
    apply intervalIntegrable_circleLogProfile
    intro z hz
    have hscaled : (r : ℂ) * z ∈ Metric.closedBall (0 : ℂ) 1 := by
      have hz1 : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      rw [Metric.mem_closedBall, dist_zero_right, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
      exact (mul_le_mul_of_nonneg_left hz1 hr.1.le).trans (by simpa only [mul_one] using hr.2.le)
    exact (hdψ q _ hscaled).comp' (analyticAt_const.mul analyticAt_id)
  have hJ (q t : Fin s) : Tendsto (fun r : ℝ => pairwiseMaxIntegral (f r q) (f r t))
      (𝓝[<] 1) (𝓝 (pairwiseMaxIntegral (f₀ q) (f₀ t))) :=
    tendsto_pairwiseMaxIntegral_of_L1 (hbase q) (hbase t) (hint q) (hint t)
      (tendsto_L1_circleLogProfile_radial (hdψ q) (hderiv q))
      (tendsto_L1_circleLogProfile_radial (hdψ t) (hderiv t))
  have hright : Tendsto (fun r : ℝ => 14 * (16603 / 3920 : ℝ) +
      ∑ q : Fin s, ∑ t : Fin s, (v q.succ - v q.castSucc) * (v t.succ - v t.castSucc) *
        pairwiseMaxIntegral (f r q) (f r t)) (𝓝[<] 1)
      (𝓝 (14 * (16603 / 3920 : ℝ) + ∑ q : Fin s, ∑ t : Fin s,
        (v q.succ - v q.castSucc) * (v t.succ - v t.castSucc) *
        pairwiseMaxIntegral (f₀ q) (f₀ t))) :=
    (tendsto_finset_sum Finset.univ (fun q _ => tendsto_finset_sum Finset.univ
      (fun t _ => (hJ q t).const_mul
        ((v q.succ - v q.castSucc) * (v t.succ - v t.castSucc))))).const_add _
  have hlog (q : Fin s) : Tendsto (fun r : ℝ => Real.log ‖(r : ℂ) * deriv (ψ q) 0‖)
      (𝓝[<] 1) (𝓝 (Real.log ‖deriv (ψ q) 0‖)) := by
    have hc : ContinuousAt (fun r : ℝ => Real.log ‖(r : ℂ) * deriv (ψ q) 0‖) 1 :=
      ((Complex.continuous_ofReal.mul continuous_const).continuousAt.norm).log (by
        simpa only [Complex.ofReal_one, one_mul] using norm_ne_zero_iff.mpr (hderiv q))
    simpa only [Complex.ofReal_one, one_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hleft : Tendsto (fun r : ℝ => 14 * ∑ q : Fin s,
      (v q.succ ^ 2 - v q.castSucc ^ 2) * Real.log ‖(r : ℂ) * deriv (ψ q) 0‖)
      (𝓝[<] 1) (𝓝 (14 * ∑ q : Fin s,
        (v q.succ ^ 2 - v q.castSucc ^ 2) * Real.log ‖deriv (ψ q) 0‖)) :=
    (tendsto_finset_sum Finset.univ
      (fun q _ => (hlog q).const_mul (v q.succ ^ 2 - v q.castSucc ^ 2))).const_mul 14
  exact le_of_tendsto_of_tendsto hleft hright
    (cdt_partition_holonomy_bound_eventually_inner_radius a₀ b₀ c₀ hrel hne
      hs v hv hv0 hv1 ψ P hψ0 hP hderiv hdψ hmero)

end DirichletL

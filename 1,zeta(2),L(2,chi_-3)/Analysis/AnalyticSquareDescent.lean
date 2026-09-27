import Mathlib

/-!
Analytic descent through the square map on the unit disc.
This supports CDT v2 `14functions`, TeX 8044-8051, after double pullback.
-/

namespace DirichletL

open Filter
open scoped Topology

theorem exists_analytic_square_descent_on_unit_ball {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1)) (hg : AnalyticAt ℂ g 0)
    (hfg : f =ᶠ[𝓝 (0 : ℂ)] fun z => g (z ^ 2)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (Metric.ball 0 1) ∧
      F =ᶠ[𝓝 (0 : ℂ)] g ∧ ∀ z : ℂ, ‖z‖ < 1 → F (z ^ 2) = f z := by
  have hneg : Tendsto (fun z : ℂ => -z) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa only [neg_zero] using (continuous_neg.tendsto (0 : ℂ))
  have hfevenLocal : (fun z => f (-z)) =ᶠ[𝓝 (0 : ℂ)] f := by
    filter_upwards [hfg, hfg.comp_tendsto hneg] with z hz hzm
    change f (-z) = g ((-z) ^ 2) at hzm
    rw [hzm, hz, neg_sq]
  have hfneg : AnalyticOnNhd ℂ (fun z => f (-z)) (Metric.ball 0 1) := by
    intro z hz
    exact (hf (-z) (by simpa using hz)).comp' analyticAt_id.neg
  have hfeven (z : ℂ) (hz : ‖z‖ < 1) : f (-z) = f z :=
    hfneg.eqOn_of_preconnected_of_eventuallyEq hf (convex_ball (0 : ℂ) 1).isPreconnected
      (by simp) hfevenLocal (by simpa using hz)
  let R (w : ℂ) := w ^ (1 / 2 : ℂ)
  have hR (w : ℂ) : R w ^ 2 = w := by
    simpa only [R, one_div] using Complex.cpow_nat_inv_pow w (n := 2) two_ne_zero
  have hRn (w : ℂ) : ‖R w‖ ^ 2 = ‖w‖ := by
    simpa only [norm_pow] using congrArg norm (hR w)
  let F (w : ℂ) := f (R w)
  have hFgerm : F =ᶠ[𝓝 (0 : ℂ)] g := by
    obtain ⟨d, hd, he⟩ := Metric.mem_nhds_iff.mp hfg
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (sq_pos_of_pos hd)] with w hw
    have hwn : ‖w‖ < d ^ 2 := by simpa using hw
    have hrd : ‖R w‖ < d := by nlinarith [hRn w, norm_nonneg (R w)]
    have h := he (by simpa using hrd)
    change f (R w) = g (R w ^ 2) at h
    simpa only [F, hR] using h
  refine ⟨F, ?_, hFgerm, ?_⟩
  · intro w hw
    by_cases hw0 : w = 0
    · subst w
      exact hg.congr hFgerm.symm
    have hwn : ‖w‖ < 1 := by simpa using hw
    let S (u : ℂ) := w ^ (1 / 2 : ℂ) * (u / w) ^ (1 / 2 : ℂ)
    have hbase : AnalyticAt ℂ (fun u : ℂ => u / w) w :=
      analyticAt_id.div analyticAt_const hw0
    have hslit : w / w ∈ Complex.slitPlane := by simp [hw0]
    have hSa : AnalyticAt ℂ S w :=
      analyticAt_const.mul (hbase.cpow analyticAt_const hslit)
    have hS (u : ℂ) : S u ^ 2 = u := by
      change (R w * R (u / w)) ^ 2 = u
      rw [mul_pow, hR, hR]
      field_simp
    have hSsmall (u : ℂ) (hu : ‖u‖ < 1) : ‖S u‖ < 1 := by
      have hn : ‖S u‖ ^ 2 = ‖u‖ := by
        simpa only [norm_pow] using congrArg norm (hS u)
      nlinarith [norm_nonneg (S u)]
    have he : (fun u => f (S u)) =ᶠ[𝓝 w] F := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hw] with u hu
      have hun : ‖u‖ < 1 := by simpa using hu
      obtain h | h := sq_eq_sq_iff_eq_or_eq_neg.mp ((hR u).trans (hS u).symm)
      · change f (S u) = f (R u)
        rw [h]
      · change f (S u) = f (R u)
        rw [h, hfeven (S u) (hSsmall u hun)]
    exact ((hf (S w) (by simpa using hSsmall w hwn)).comp' hSa).congr he
  · intro z hz
    obtain h | h := sq_eq_sq_iff_eq_or_eq_neg.mp (hR (z ^ 2))
    · change f (R (z ^ 2)) = f z
      rw [h]
    · change f (R (z ^ 2)) = f z
      rw [h, hfeven z hz]

end DirichletL

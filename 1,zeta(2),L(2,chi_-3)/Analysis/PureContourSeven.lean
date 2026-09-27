import Analysis.PureOriginalReconstruction
import Analysis.AnalyticSquareDescent
import Analysis.AnalyticLinearODEAnnulus
import Analysis.ContourQuadraticLift

/-!
Actual B1 through B7 on the contour parameter disc.
Source: CDT v2 `defB`, `defB5`, `defB67`, and `14functions` at 8044-8051.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_analytic_cdtContour_pure_double_pullback :
    ∃ F : Fin 7 → ℂ → ℂ,
      (∀ j, AnalyticOnNhd ℂ (F j) (Metric.ball 0 1)) ∧
      ∀ j, F j =ᶠ[𝓝 (0 : ℂ)] fun z =>
        pureSevenDescentFamily j (cdtContourMap (z ^ 2)) := by
  obtain ⟨X, hXa, hX0, hX1, hXzero, hY, _, _⟩ :=
    exists_analytic_cdtContour_original_coordinate
  have hXat (z : ℂ) (hz : ‖z‖ < 1) : AnalyticAt ℂ X z := hXa z (by simpa using hz)
  have hXt : Tendsto X (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa only [hX0] using (hXat 0 (by norm_num)).continuousAt.tendsto
  have hXtp : Tendsto X (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hXt.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ)
      (by norm_num : (0 : ℝ) < 1)), self_mem_nhdsWithin] with z hz hz0
    change X z ≠ 0
    exact fun he => hz0 ((hXzero z (by simpa using hz)).mp he)
  let M (z : ℂ) := deriv X z • pureOriginalMatrix (X z)
  let f (z : ℂ) := pureOriginalState (X z)
  have hf0 : AnalyticAt ℂ f 0 :=
    analyticAt_pureOriginalState_zero.comp_of_eq (hXat 0 (by norm_num)) hX0
  have hMa (z : ℂ) (hz0 : z ≠ 0) (hz : ‖z‖ < 1) : AnalyticAt ℂ M z :=
    (hXat z hz).deriv.smul ((analyticAt_pureOriginalMatrix
      (fun he => hz0 ((hXzero z hz).mp he)) (hX1 z hz)).comp' (hXat z hz))
  have hfo : ∀ᶠ z : ℂ in 𝓝[≠] 0, HasDerivAt f (M z *ᵥ f z) z := by
    filter_upwards [hXtp.eventually eventually_hasDerivAt_pureOriginalState,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ)
        (by norm_num : (0 : ℝ) < 1))] with z hz hz1
    simpa only [f, M, Matrix.smul_mulVec_assoc, Function.comp_apply] using
      hz.scomp z (hXat z (by simpa using hz1)).differentiableAt.hasDerivAt
  have hfo' : ∀ᶠ z : ℂ in 𝓝 0, z ≠ 0 → HasDerivAt f (M z *ᵥ f z) z :=
    eventually_nhdsWithin_iff.mp hfo
  obtain ⟨s, hs, hlocal⟩ := Metric.mem_nhds_iff.mp (hf0.eventually_analyticAt.and hfo')
  let r : ℝ := min s (1 / 2)
  have hr : 0 < r := lt_min hs (by norm_num)
  have hrs : r ≤ s := min_le_left _ _
  have hr1 : r < 1 := (min_le_right s (1 / 2)).trans_lt (by norm_num)
  have hf : AnalyticOnNhd ℂ f (Metric.ball 0 r) := by
    intro z hz
    exact (hlocal (Metric.ball_subset_ball hrs hz)).1
  have hM : AnalyticOnNhd ℂ M {z : ℂ | r / 2 < ‖z‖ ∧ ‖z‖ < 1} := by
    intro z hz
    apply hMa z _ hz.2
    exact norm_pos_iff.mp ((half_pos hr).trans hz.1)
  have hode (z : ℂ) (hza : r / 2 < ‖z‖) (hzr : ‖z‖ < r) :
      HasDerivAt f (M z *ᵥ f z) z :=
    (hlocal (by simpa using hzr.trans_le hrs)).2
      (norm_pos_iff.mp ((half_pos hr).trans hza))
  obtain ⟨V, hVa, hVeq, _⟩ := exists_analytic_matrix_extension_on_ball
    (half_pos hr) (half_lt_self hr) hr1 hM hf hode
  have hVlocal : V =ᶠ[𝓝 (0 : ℂ)] f := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
    exact hVeq hz
  let F (j : Fin 7) (z : ℂ) := pureOriginalReconstruct (X z) (V z) j
  refine ⟨F, ?_, ?_⟩
  · intro j z hz
    have hzn : ‖z‖ < 1 := by simpa using hz
    exact analyticAt_pi_iff.mp
      (analyticAt_pureOriginalReconstruct (hXat z hzn) (hVa z hz) (hX1 z hzn)) j
  · intro j
    filter_upwards [hVlocal, pureOriginalReconstruct_state_germ.comp_tendsto hXt,
      Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hzV hzP hz
    change V z = pureOriginalState (X z) at hzV
    change pureOriginalReconstruct (X z) (V z) j = _
    rw [hzV]
    have h := congrFun hzP j
    dsimp only [Function.comp_apply] at h
    rw [pureSevenState_apply, hY z (by simpa using hz)] at h
    exact h

theorem exists_analytic_cdtContour_pure_pullback :
    ∃ F : Fin 7 → ℂ → ℂ,
      (∀ j, AnalyticOnNhd ℂ (F j) (Metric.ball 0 1)) ∧
      ∀ j, F j =ᶠ[𝓝 (0 : ℂ)] fun z =>
        pureSevenDescentFamily j (cdtContourMap z) := by
  classical
  obtain ⟨F, hFa, hFg⟩ := exists_analytic_cdtContour_pure_double_pullback
  have hg (j : Fin 7) : AnalyticAt ℂ
      (fun z => pureSevenDescentFamily j (cdtContourMap z)) 0 := by
    have hj : AnalyticAt ℂ (pureSevenDescentFamily j) 0 := by
      simpa only [pureSevenState_apply] using
        analyticAt_pi_iff.mp analyticAt_pureSevenState_zero j
    exact hj.comp_of_eq (analyticOnNhd_cdtContourMap 0 (by simp)) cdtContourMap_zero
  choose G hG using fun j : Fin 7 =>
    exists_analytic_square_descent_on_unit_ball (hFa j) (hg j) (hFg j)
  exact ⟨G, fun j => (hG j).1, fun j => (hG j).2.1⟩

end DirichletL

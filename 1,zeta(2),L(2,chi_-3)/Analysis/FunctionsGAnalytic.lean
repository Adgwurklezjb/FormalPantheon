import Analysis.FunctionsHOverconvergence
import Analysis.MobiusDescentAnalytic
import Analysis.ZagierPullbackRegularity
import Analysis.ZagierSheetPaths

/-!
The actual symmetrized sum in CDT v2, Definition `defG`, and a common initial
neighborhood for the two H branches used in Lemma `14functions`.
-/

namespace DirichletL

open Filter
open scoped Topology ENNReal

/-- The analytic sum of the literal rational G-series in CDT Definition `defG`. -/
noncomputable def gLinearCombinationAnalytic (a b c : ℚ) : ℂ → ℂ :=
  symmetrizedAnalytic (a • hA + b • hB + c • hC)

theorem analyticAt_gLinearCombinationAnalytic_zero (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0) :
    AnalyticAt ℂ (gLinearCombinationAnalytic a b c) 0 :=
  analyticAt_symmetrizedAnalytic_of_pos_radius _
    (zero_lt_one.trans_le (one_le_radius_h_linearCombination a b c hrel))

theorem gLinearCombinationAnalytic_pullback (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0) :
    (gLinearCombinationAnalytic a b c ∘ mobiusCoordinate) =ᶠ[𝓝 0]
      (fun x => hLinearCombinationAnalytic a b c x +
        hLinearCombinationAnalytic a b c (mobiusAnalyticInvolution x)) :=
  symmetrizedAnalytic_pullback_of_pos_radius _
    (zero_lt_one.trans_le (one_le_radius_h_linearCombination a b c hrel))

/-- A common positive neighborhood gives the actual initial germs on both sheets. -/
theorem exists_gLinearCombination_initial_radius (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : ℂ, ‖x‖ < R →
      ‖x‖ < 1 ∧ ‖mobiusAnalyticInvolution x‖ < 1 ∧
      AnalyticAt ℂ (gLinearCombinationAnalytic a b c) (mobiusCoordinate x) ∧
      (gLinearCombinationAnalytic a b c ∘ mobiusCoordinate) =ᶠ[𝓝 x]
        (fun z => hLinearCombinationAnalytic a b c z +
          hLinearCombinationAnalytic a b c (mobiusAnalyticInvolution z)) ∧
      (x ≠ 0 → x ∈ zagierPullbackRegularSet) := by
  have hi : ContinuousAt mobiusAnalyticInvolution (0 : ℂ) :=
    (analyticAt_mobiusAnalyticInvolution (by norm_num)).continuousAt
  have hY : Tendsto mobiusCoordinate (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa only [mobiusCoordinate_zero] using
      (analyticAt_mobiusCoordinate (by norm_num : (0 : ℂ) ≠ 1)).continuousAt.tendsto
  have hG := hY.eventually (analyticAt_gLinearCombinationAnalytic_zero a b c hrel).eventually_analyticAt
  have hx : ∀ᶠ x : ℂ in 𝓝 0, ‖x‖ < 1 :=
    continuousAt_id.norm.eventually_lt_const (by norm_num)
  have hw : ∀ᶠ x : ℂ in 𝓝 0, ‖mobiusAnalyticInvolution x‖ < 1 :=
    hi.norm.eventually_lt_const (by norm_num [mobiusAnalyticInvolution])
  have he := (gLinearCombinationAnalytic_pullback a b c hrel).eventually_nhds
  have hn := eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ 1)
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp
    (hx.and (hw.and (hG.and (he.and (hn.and eventually_mobiusCoordinate_regular_zero)))))
  refine ⟨R, hR, ?_⟩
  intro x hxr
  obtain ⟨hx, hw, hG, he, hn, hreg⟩ :=
    hball (by simpa only [Metric.mem_ball, dist_zero_right] using hxr)
  exact ⟨hx, hw, hG, he, fun hx0 => ⟨hn, hreg hx0⟩⟩

end DirichletL

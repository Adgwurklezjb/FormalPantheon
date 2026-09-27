import Analysis.MobiusAnalyticCoordinate
import Analysis.ZagierCompanionSystem
import Analysis.ZagierEndpointLoop

/-!
Regularity of the projected endpoint loops for CDT v2 equations `y in x`
and `explicitode`. All extra cubic singularities are excluded explicitly.
-/

namespace DirichletL

open Filter Set unitInterval
open scoped Topology

@[simp] theorem mobiusCoordinate_zero : mobiusCoordinate 0 = 0 := by
  norm_num [mobiusCoordinate]

@[simp] theorem mobiusCoordinate_two : mobiusCoordinate 2 = 4 := by
  norm_num [mobiusCoordinate]

theorem mobiusCoordinate_one_div_nine : mobiusCoordinate (1 / 9) = -1 / 72 := by
  norm_num [mobiusCoordinate]

theorem mobiusCoordinate_regular_ne_zero_two {z : ℂ}
    (hz : mobiusCoordinate z ∈ zagierODERegularSet) : z ≠ 0 ∧ z ≠ 2 := by
  obtain ⟨hz₀, hz₄, _⟩ := (mem_zagierODERegularSet_iff _).mp hz
  constructor
  · intro he
    exact hz₀ (by rw [he, mobiusCoordinate_zero])
  · intro he
    exact hz₄ (by rw [he, mobiusCoordinate_two])

theorem mobiusCoordinate_ne_zero {z : ℂ} (hz₀ : z ≠ 0) (hz₁ : z ≠ 1) :
    mobiusCoordinate z ≠ 0 := by
  intro h
  have he : z * z = 0 := by
    dsimp [mobiusCoordinate] at h
    field_simp [sub_ne_zero.mpr hz₁] at h
    linear_combination h
  exact mul_ne_zero hz₀ hz₀ he

theorem mobiusCoordinate_ne_neg_one_div_seventy_two {z : ℂ} (hz₁ : z ≠ 1)
    (hz₉ : z ≠ 1 / 9) (hz₈ : z ≠ -1 / 8) : mobiusCoordinate z ≠ -1 / 72 := by
  intro h
  have he : (9 * z - 1) * (8 * z + 1) = 0 := by
    dsimp [mobiusCoordinate] at h
    field_simp [sub_ne_zero.mpr hz₁] at h
    linear_combination h
  rcases mul_eq_zero.mp he with he | he
  · apply hz₉
    linear_combination (1 / 9 : ℂ) * he
  · apply hz₈
    linear_combination (1 / 8 : ℂ) * he

theorem eventually_mobiusCoordinate_regular_zero :
    ∀ᶠ z : ℂ in 𝓝 0, z ≠ 0 → mobiusCoordinate z ∈ zagierODERegularSet := by
  have hc : ContinuousAt mobiusCoordinate (0 : ℂ) :=
    (analyticAt_mobiusCoordinate (by norm_num)).continuousAt
  have h₄ : ∀ᶠ z : ℂ in 𝓝 0, mobiusCoordinate z ≠ 4 :=
    hc.eventually_ne (by norm_num)
  have h₇₂ : ∀ᶠ z : ℂ in 𝓝 0, mobiusCoordinate z ≠ -1 / 72 :=
    hc.eventually_ne (by norm_num)
  have hQ : ∀ᶠ z : ℂ in 𝓝 0, zagierSingularCubic.eval (mobiusCoordinate z) ≠ 0 :=
    (zagierSingularCubic.continuous.continuousAt.comp hc).eventually_ne
      (by norm_num [eval_zero_zagierSingularCubic])
  filter_upwards [eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ 1), h₄, h₇₂, hQ]
    with z hz₁ hz₄ hz₇₂ hzQ
  intro hz₀
  exact (mem_zagierODERegularSet_iff _).mpr
    ⟨mobiusCoordinate_ne_zero hz₀ hz₁, hz₄, hz₇₂, hzQ⟩

theorem eventually_mobiusCoordinate_regular_one_div_nine :
    ∀ᶠ z : ℂ in 𝓝 (1 / 9), z ≠ 1 / 9 → mobiusCoordinate z ∈ zagierODERegularSet := by
  have hc : ContinuousAt mobiusCoordinate (1 / 9 : ℂ) :=
    (analyticAt_mobiusCoordinate (by norm_num)).continuousAt
  have h₀ : ∀ᶠ z : ℂ in 𝓝 (1 / 9), mobiusCoordinate z ≠ 0 :=
    hc.eventually_ne (by rw [mobiusCoordinate_one_div_nine]; norm_num)
  have h₄ : ∀ᶠ z : ℂ in 𝓝 (1 / 9), mobiusCoordinate z ≠ 4 :=
    hc.eventually_ne (by rw [mobiusCoordinate_one_div_nine]; norm_num)
  have hQ : ∀ᶠ z : ℂ in 𝓝 (1 / 9), zagierSingularCubic.eval (mobiusCoordinate z) ≠ 0 :=
    (zagierSingularCubic.continuous.continuousAt.comp hc).eventually_ne (by
      rw [Function.comp_apply, mobiusCoordinate_one_div_nine,
        eval_neg_one_div_seventy_two_zagierSingularCubic]
      norm_num)
  filter_upwards [eventually_ne_nhds (by norm_num : (1 / 9 : ℂ) ≠ 1),
    eventually_ne_nhds (by norm_num : (1 / 9 : ℂ) ≠ -1 / 8), h₀, h₄, hQ]
    with z hz₁ hz₈ hz₀ hz₄ hzQ
  intro hz₉
  exact (mem_zagierODERegularSet_iff _).mpr
    ⟨hz₀, hz₄, mobiusCoordinate_ne_neg_one_div_seventy_two hz₁ hz₉ hz₈, hzQ⟩

theorem exists_zagierPullback_circle_radius :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, ∀ hr : r ∈ Ioo 0 (1 / 9 : ℝ), r < R → ∀ t : I,
      mobiusCoordinate (complexCirclePath r t) ∈ zagierODERegularSet ∧
      mobiusCoordinate (zagierEndpointCirclePath r hr t) ∈ zagierODERegularSet := by
  have hT : Tendsto zagierEndpointCoordinate (𝓝 (0 : ℂ)) (𝓝 (1 / 9 : ℂ)) := by
    simpa only [zagierEndpointCoordinate_zero, one_div] using
      (analyticAt_zagierEndpointCoordinate (by norm_num : (0 : ℂ) ≠ 1)).continuousAt.tendsto
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp
    (eventually_mobiusCoordinate_regular_zero.and
      (hT.eventually eventually_mobiusCoordinate_regular_one_div_nine))
  refine ⟨R, hR, ?_⟩
  intro r hr hrR t
  have hm : complexCirclePath r t ∈ Metric.ball (0 : ℂ) R := by
    simpa only [Metric.mem_ball, dist_zero_right, norm_complexCirclePath,
      abs_of_pos hr.1] using hrR
  have hz : complexCirclePath r t ≠ 0 := by
    intro he
    have hreg := zagierSecondOrder_circle_regular r hr t
    simp only [he, zero_mul, ne_eq, not_true_eq_false] at hreg
  have hzT : zagierEndpointCoordinate (complexCirclePath r t) ≠ 1 / 9 := by
    intro he
    have hreg := zagierSecondOrder_endpointCircle_regular r hr t
    simp only [zagierEndpointCirclePath_apply, he] at hreg
    norm_num at hreg
  exact ⟨(hball hm).1 hz, (hball hm).2 hzT⟩

end DirichletL

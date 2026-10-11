import Analysis.AnalyticContinuationDifference

/-!
Polynomial relations of actual analytic continuations, including transfer
from a punctured germ to a regular base, for CDT v2, Lemma `14functions`
(supplied TeX 8044-8100).
-/

namespace DirichletL

open Filter Set
open scoped Topology

namespace AnalyticContinuationAlong

theorem finset_sum {ι T : Type*} [TopologicalSpace T] (s : Finset ι)
    {γ : T → ℂ} (hγ : Continuous γ) {F : ι → T → ℂ → ℂ}
    (hF : ∀ i ∈ s, AnalyticContinuationAlong γ (F i)) :
    AnalyticContinuationAlong γ (fun t z => ∑ i ∈ s, F i t z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        AnalyticContinuationAlong.const hγ (F := fun _ => (0 : ℂ))
          (fun _ => analyticAt_const)
  | @insert i s hi ih =>
      have hiF := hF i (Finset.mem_insert_self _ _)
      have hsF := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using hiF.add hsF

theorem polynomial_sum {ι T : Type*} [Fintype ι] [TopologicalSpace T]
    {γ : T → ℂ} (hγ : Continuous γ) (P : ι → Polynomial ℂ)
    {F : ι → T → ℂ → ℂ} (hF : ∀ i, AnalyticContinuationAlong γ (F i)) :
    AnalyticContinuationAlong γ (fun t z => ∑ i, (P i).eval z * F i t z) := by
  apply finset_sum Finset.univ hγ
  intro i _
  have hP : AnalyticContinuationAlong γ (fun _ z => (P i).eval z) := by
    apply AnalyticContinuationAlong.const hγ
    intro t
    exact AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (P i) (γ t) (mem_univ _)
  exact hP.mul (hF i)

theorem polynomial_relation {ι T : Type*} [Fintype ι] [TopologicalSpace T]
    [PreconnectedSpace T] {γ : T → ℂ} (hγ : Continuous γ) (P : ι → Polynomial ℂ)
    {F : ι → T → ℂ → ℂ} (hF : ∀ i, AnalyticContinuationAlong γ (F i))
    {t0 : T} (h0 : (fun z => ∑ i, (P i).eval z * F i t0 z) =ᶠ[𝓝 (γ t0)] 0) (t : T) :
    (fun z => ∑ i, (P i).eval z * F i t z) =ᶠ[𝓝 (γ t)] 0 :=
  (polynomial_sum hγ P hF).eq_of_preconnectedSpace
    (AnalyticContinuationAlong.const hγ (fun _ => analyticAt_const)) h0 t

end AnalyticContinuationAlong

theorem exists_radius_eventuallyEq_zero_of_punctured {f : ℂ → ℂ} {z0 : ℂ}
    (hf : f =ᶠ[𝓝[≠] z0] 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, dist z z0 < r → z ≠ z0 → f =ᶠ[𝓝 z] 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp hf
  refine ⟨r, hr, ?_⟩
  intro z hz hne
  filter_upwards [Metric.isOpen_ball.mem_nhds hz, eventually_ne_nhds hne] with w hw hwne
  exact hball ⟨hw, hwne⟩

end DirichletL

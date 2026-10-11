import Analysis.ZagierEndpointMonodromy
import Analysis.ZagierSolutionSummands

/-!
The source summand and its monodromy orbit span in CDT v2, `14functions`.
The two actual endpoint germs span every source solution germ on the interval.
-/

namespace DirichletL

open Filter Set
open scoped Topology

theorem zagierSourceSummand_eq_span_endpoint {r : ℝ}
    (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) (φ ψ : zagierSolutionGerms (mobiusCoordinate r))
    (hφ : mobiusGermPullback (zagierEndpointInterval_noncritical hr).2.1
      (φ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = zagierAnalytic)
    (hψ : mobiusGermPullback (zagierEndpointInterval_noncritical hr).2.1
      (ψ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = zagierEndpointSolution) :
    zagierSourceSummand (zagierEndpointInterval_noncritical hr).2.1 =
      Submodule.span ℂ {φ, ψ} := by
  obtain ⟨hr₀, hr₁, hr₂⟩ := zagierEndpointInterval_noncritical hr
  obtain ⟨hH, hHo, hS, hSo⟩ := zagierEndpointInterval_solutions hr
  have hreg := (zagierSecondOrder_leading_ne_zero_of_pullback_regular hr₁
    (mobiusCoordinate_regular_of_mem_Ioo hr)).1
  apply le_antisymm
  · rintro χ ⟨f, hf, hfo, hχ⟩
    have he := eventuallyEq_zagierSecondOrder_basis hf hH hS hreg hfo hHo hSo
      (zagierEndpointSolution_wronskian_ne_zero hr)
    obtain ⟨a, b, hab⟩ : ∃ a b : ℂ,
        f =ᶠ[𝓝 (r : ℂ)] fun w => a * zagierAnalytic w + b * zagierEndpointSolution w :=
      ⟨_, _, he⟩
    apply Submodule.mem_span_pair.mpr
    refine ⟨a, b, ?_⟩
    apply Subtype.ext
    apply mobiusGermPullback_injective hr₀ hr₁ hr₂
    simp only [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, hφ, hψ, hχ]
    exact (Germ.coe_eq.mpr hab).symm
  · apply Submodule.span_le.mpr
    intro χ hχ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hχ
    rcases hχ with rfl | rfl
    · exact ⟨zagierAnalytic, hH, hHo, hφ⟩
    · exact ⟨zagierEndpointSolution, hS, hSo, hψ⟩

theorem zagierSourceSummand_le_orbitSpan_of_mem {r : ℝ}
    (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) {χ : zagierSolutionGerms (mobiusCoordinate r)}
    (hχ : χ ∈ zagierSourceSummand (zagierEndpointInterval_noncritical hr).2.1) (hne : χ ≠ 0) :
    zagierSourceSummand (zagierEndpointInterval_noncritical hr).2.1 ≤
      zagierMonodromyOrbitSpan ⟨mobiusCoordinate r, mobiusCoordinate_regular_of_mem_Ioo hr⟩ χ := by
  obtain ⟨φ, ψ, hφ, hψ, _, horbit⟩ := exists_zagierEndpoint_commonBase_orbitSpan hr
  have hspan := zagierSourceSummand_eq_span_endpoint hr φ ψ hφ hψ
  rw [hspan] at hχ ⊢
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hχ
  apply horbit a b
  by_contra hab
  push_neg at hab
  exact hne (by simp only [hab.1, hab.2, zero_smul, add_zero])

end DirichletL

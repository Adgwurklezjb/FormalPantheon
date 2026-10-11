import Analysis.ZagierPullbackBasis

/-!
The unique analytic decomposition behind CDT v2's `14functions` monodromy argument.
The two summands solve the source and Mobius-conjugate second-order equations.
-/

namespace DirichletL

open Filter
open scoped Topology

theorem exists_zagierPullback_decomposition {x : ℂ} (hx : x ≠ 1)
    (hreg : mobiusCoordinate x ∈ zagierODERegularSet)
    (φ : zagierSolutionGerms (mobiusCoordinate x)) :
    ∃ f g : ℂ → ℂ, AnalyticAt ℂ f x ∧ AnalyticAt ℂ g x ∧
      zagierSecondOrderODE f =ᶠ[𝓝 x] 0 ∧ zagierConjugateAnalyticODE g =ᶠ[𝓝 x] 0 ∧
      mobiusGermPullback hx (φ : Germ (𝓝 (mobiusCoordinate x)) ℂ) =
        (fun w => f w + g w : ℂ → ℂ) := by
  obtain ⟨b, F, G, hF, hG⟩ := exists_zagierPullback_basis hx hreg
  let c : Fin 2 ⊕ Fin 2 → ℂ := b.repr φ
  let f : ℂ → ℂ := fun w => c (Sum.inl 0) * F 0 w + c (Sum.inl 1) * F 1 w
  let g : ℂ → ℂ := fun w => c (Sum.inr 0) * G 0 w + c (Sum.inr 1) * G 1 w
  refine ⟨f, g,
    ((hF 0).1.const_smul (c := c (Sum.inl 0))).add
      ((hF 1).1.const_smul (c := c (Sum.inl 1))),
    ((hG 0).1.const_smul (c := c (Sum.inr 0))).add
      ((hG 1).1.const_smul (c := c (Sum.inr 1))), ?_, ?_, ?_⟩
  · filter_upwards [(hF 0).1.eventually_analyticAt, (hF 1).1.eventually_analyticAt,
      (hF 0).2.1, (hF 1).2.1] with w hw₀ hw₁ he₀ he₁
    simp [f, zagierSecondOrderODE_linearCombination hw₀ hw₁, he₀, he₁]
  · filter_upwards [(hG 0).1.eventually_analyticAt, (hG 1).1.eventually_analyticAt,
      (hG 0).2.1, (hG 1).2.1] with w hw₀ hw₁ he₀ he₁
    simp [g, zagierConjugateAnalyticODE_linearCombination hw₀ hw₁, he₀, he₁]
  · have he := congrArg (fun u : zagierSolutionGerms (mobiusCoordinate x) =>
      mobiusGermPullback hx (u : Germ (𝓝 (mobiusCoordinate x)) ℂ)) (b.sum_repr φ)
    simp only [Fintype.sum_sum_type, Fin.sum_univ_two, Submodule.coe_add,
      Submodule.coe_smul, map_add, map_smul, (hF 0).2.2, (hF 1).2.2,
      (hG 0).2.2, (hG 1).2.2] at he
    exact he.symm

theorem eventuallyEq_zagierPullback_decomposition {f g u v : ℂ → ℂ} {x : ℂ}
    (hx : x ≠ 1) (hreg : mobiusCoordinate x ∈ zagierODERegularSet)
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x)
    (hu : AnalyticAt ℂ u x) (hv : AnalyticAt ℂ v x)
    (hfE : zagierSecondOrderODE f =ᶠ[𝓝 x] 0)
    (hgC : zagierConjugateAnalyticODE g =ᶠ[𝓝 x] 0)
    (huE : zagierSecondOrderODE u =ᶠ[𝓝 x] 0)
    (hvC : zagierConjugateAnalyticODE v =ᶠ[𝓝 x] 0)
    (he : (fun w => f w + g w) =ᶠ[𝓝 x] fun w => u w + v w) :
    f =ᶠ[𝓝 x] u ∧ g =ᶠ[𝓝 x] v := by
  have hFE : zagierSecondOrderODE (f - u) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hf.eventually_analyticAt, hu.eventually_analyticAt, hfE, huE]
      with w hwf hwu he₀ he₁
    simpa [sub_eq_add_neg, he₀, he₁] using
      zagierSecondOrderODE_linearCombination hwf hwu 1 (-1)
  have hsub : f - u =ᶠ[𝓝 x] fun w => v w - g w := by
    filter_upwards [he] with w hw
    change f w - u w = v w - g w
    linear_combination hw
  have hFC : zagierConjugateAnalyticODE (f - u) =ᶠ[𝓝 x] 0 := by
    apply (eventuallyEq_zagierConjugateAnalyticODE hsub).trans
    filter_upwards [hv.eventually_analyticAt, hg.eventually_analyticAt, hvC, hgC]
      with w hwv hwg he₀ he₁
    simpa [sub_eq_add_neg, he₀, he₁] using
      zagierConjugateAnalyticODE_linearCombination hwv hwg 1 (-1)
  have hzero := eventuallyEq_zero_of_zagierSecondOrder_and_conjugate hx hreg
    (hf.sub hu) hFE hFC
  constructor
  · filter_upwards [hzero] with w hw
    exact sub_eq_zero.mp hw
  · filter_upwards [he, hzero] with w hw hzw
    change f w - u w = 0 at hzw
    linear_combination hw - hzw

end DirichletL

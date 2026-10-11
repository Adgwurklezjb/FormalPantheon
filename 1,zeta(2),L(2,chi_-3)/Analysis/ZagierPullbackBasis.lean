import Analysis.MobiusGermPullback
import Analysis.ZagierEndpointContinuation
import Analysis.ZagierPullbackSeparation

/-!
A basis adapted to the analytic second-order summands of CDT v2's `explicitode`.
This supplies the actual four-dimensional decomposition used in `14functions`.
-/

namespace DirichletL

open Filter
open scoped Topology

private theorem eq_zero_of_normalized_analytic_pair {f : Fin 2 → ℂ → ℂ} {z : ℂ}
    (hf : ∀ j, AnalyticAt ℂ (f j) z)
    (hv : ∀ j, f j z = if j = 0 then 1 else 0)
    (hd : ∀ j, deriv (f j) z = if j = 1 then 1 else 0) {a b : ℂ}
    (he : (fun w => a * f 0 w + b * f 1 w) =ᶠ[𝓝 z] 0) : a = 0 ∧ b = 0 := by
  constructor
  · simpa [hv] using he.self_of_nhds
  · have hz : deriv (fun w => a * f 0 w + b * f 1 w) z = 0 := by
      simpa using he.deriv.self_of_nhds
    change deriv ((fun w => a * f 0 w) + (fun w => b * f 1 w)) z = 0 at hz
    have hder : deriv ((fun w => a * f 0 w) + (fun w => b * f 1 w)) z =
        a * deriv (f 0) z + b * deriv (f 1) z := by
      simpa only [Pi.add_apply] using
        (((hf 0).differentiableAt.hasDerivAt.const_mul a).fun_add
          ((hf 1).differentiableAt.hasDerivAt.const_mul b)).deriv
    rw [hder] at hz
    simpa [hd] using hz

theorem exists_zagierPullback_basis {x : ℂ} (hx : x ≠ 1)
    (hreg : mobiusCoordinate x ∈ zagierODERegularSet) :
    ∃ (b : Module.Basis (Fin 2 ⊕ Fin 2) ℂ (zagierSolutionGerms (mobiusCoordinate x)))
      (f g : Fin 2 → ℂ → ℂ),
      (∀ j, AnalyticAt ℂ (f j) x ∧ zagierSecondOrderODE (f j) =ᶠ[𝓝 x] 0 ∧
        mobiusGermPullback hx (b (Sum.inl j) : Germ (𝓝 (mobiusCoordinate x)) ℂ) = f j) ∧
      (∀ j, AnalyticAt ℂ (g j) x ∧ zagierConjugateAnalyticODE (g j) =ᶠ[𝓝 x] 0 ∧
        mobiusGermPullback hx (b (Sum.inr j) : Germ (𝓝 (mobiusCoordinate x)) ℂ) = g j) := by
  classical
  obtain ⟨hx₀, hx₂⟩ := mobiusCoordinate_regular_ne_zero_two hreg
  obtain ⟨ha, hA⟩ := zagierSecondOrder_leading_ne_zero_of_pullback_regular hx hreg
  choose f hf hfv hfd hfo using fun j : Fin 2 =>
    exists_analytic_zagierSecondOrder_ode ha (if j = 0 then 1 else 0)
      (if j = 1 then 1 else 0)
  choose g hg hgv hgd hgo using fun j : Fin 2 =>
    exists_analytic_zagierConjugate_ode hA (if j = 0 then 1 else 0)
      (if j = 1 then 1 else 0)
  choose φ hφ using fun j =>
    exists_zagierSolutionGerm_mobiusPullback hx₀ hx hx₂ (hf j) (hfo j)
  have hglift (j : Fin 2) : ∃ ψ : zagierSolutionGerms (mobiusCoordinate x),
      mobiusGermPullback hx (ψ : Germ (𝓝 (mobiusCoordinate x)) ℂ) = g j := by
    obtain ⟨u, hu, huo, hue⟩ := exists_zagierAnalyticODE_of_pullback hx₀ hx hx₂ (hg j)
      (eventually_zagierPullbackAnalyticODE_of_conjugate hx (hg j) (hgo j))
    exact ⟨zagierSolutionGermOfFun u hu huo, Germ.coe_eq.mpr hue⟩
  choose ψ hψ using hglift
  have hli : LinearIndependent ℂ (Sum.elim φ ψ) := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have he := congrArg (fun u : zagierSolutionGerms (mobiusCoordinate x) =>
      mobiusGermPullback hx (u : Germ (𝓝 (mobiusCoordinate x)) ℂ)) hc
    simp only [Fintype.sum_sum_type, Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr,
      Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero,
      map_add, map_smul, map_zero, hφ, hψ] at he
    have hsum : (fun w => (c (Sum.inl 0) * f 0 w + c (Sum.inl 1) * f 1 w) +
        (c (Sum.inr 0) * g 0 w + c (Sum.inr 1) * g 1 w)) =ᶠ[𝓝 x] 0 :=
      Germ.coe_eq.mp he
    let F : ℂ → ℂ := fun w => c (Sum.inl 0) * f 0 w + c (Sum.inl 1) * f 1 w
    let G : ℂ → ℂ := fun w => c (Sum.inr 0) * g 0 w + c (Sum.inr 1) * g 1 w
    have hF : AnalyticAt ℂ F x :=
      ((hf 0).const_smul (c := c (Sum.inl 0))).add
        ((hf 1).const_smul (c := c (Sum.inl 1)))
    have hFE : zagierSecondOrderODE F =ᶠ[𝓝 x] 0 := by
      filter_upwards [(hf 0).eventually_analyticAt, (hf 1).eventually_analyticAt,
        hfo 0, hfo 1] with w hw₀ hw₁ he₀ he₁
      simp [F, zagierSecondOrderODE_linearCombination hw₀ hw₁, he₀, he₁]
    have hneg : F =ᶠ[𝓝 x] fun w =>
        (-c (Sum.inr 0)) * g 0 w + (-c (Sum.inr 1)) * g 1 w := by
      filter_upwards [hsum] with w hw
      dsimp only [F]
      dsimp only [Pi.zero_apply] at hw
      linear_combination hw
    have hFC : zagierConjugateAnalyticODE F =ᶠ[𝓝 x] 0 := by
      apply (eventuallyEq_zagierConjugateAnalyticODE hneg).trans
      filter_upwards [(hg 0).eventually_analyticAt, (hg 1).eventually_analyticAt,
        hgo 0, hgo 1] with w hw₀ hw₁ he₀ he₁
      rw [zagierConjugateAnalyticODE_linearCombination hw₀ hw₁]
      simp [he₀, he₁]
    have hF₀ := eventuallyEq_zero_of_zagierSecondOrder_and_conjugate hx hreg hF hFE hFC
    have hG₀ : G =ᶠ[𝓝 x] 0 := by
      filter_upwards [hsum, hF₀] with w hw hFw
      change F w + G w = 0 at hw
      simpa only [hFw, Pi.zero_apply, zero_add] using hw
    have hcf := eq_zero_of_normalized_analytic_pair hf hfv hfd hF₀
    have hcg := eq_zero_of_normalized_analytic_pair hg hgv hgd hG₀
    rcases i with j | j <;> fin_cases j
    · exact hcf.1
    · exact hcf.2
    · exact hcg.1
    · exact hcg.2
  let b := basisOfLinearIndependentOfCardEqFinrank hli
    (by simp [finrank_zagierSolutionGerms hreg])
  refine ⟨b, f, g, ?_, ?_⟩
  · intro j
    exact ⟨hf j, hfo j, by simpa [b] using hφ j⟩
  · intro j
    exact ⟨hg j, hgo j, by simpa [b] using hψ j⟩

end DirichletL

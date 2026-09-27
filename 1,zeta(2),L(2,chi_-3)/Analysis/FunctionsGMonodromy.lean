import Analysis.FunctionsGContinuation
import Analysis.ZagierPullbackAnalytic
import Analysis.ZagierSolutionGerms

/-!
The homogeneous branch difference in CDT v2, Lemma `14functions`.
The original forcing cancels on each sheet, and the two homogeneous
descents place the actual trace difference in the fourth-order solution space.
-/

namespace DirichletL

open Filter
open scoped Topology

theorem zagierSecondOrderODE_sub {f g : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) :
    zagierSecondOrderODE (f - g) x = zagierSecondOrderODE f x - zagierSecondOrderODE g x := by
  have h₁ : deriv (f - g) x = deriv f x - deriv g x :=
    deriv_sub hf.differentiableAt hg.differentiableAt
  have he : deriv (f - g) =ᶠ[𝓝 x] deriv f - deriv g := by
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with z hfz hgz
    exact deriv_sub hfz.differentiableAt hgz.differentiableAt
  have h₂ : deriv (deriv (f - g)) x = deriv (deriv f) x - deriv (deriv g) x :=
    he.deriv_eq.trans (deriv_sub hf.deriv.differentiableAt hg.deriv.differentiableAt)
  simp only [zagierSecondOrderODE, h₁, h₂, Pi.sub_apply]
  ring

theorem eventually_zagierSecondOrderODE_sub_eq_zero {f g : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x)
    (he : zagierSecondOrderODE f =ᶠ[𝓝 x] zagierSecondOrderODE g) :
    zagierSecondOrderODE (f - g) =ᶠ[𝓝 x] 0 := by
  filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt, he] with z hfz hgz hz
  simp only [zagierSecondOrderODE_sub hfz hgz, hz, sub_self, Pi.zero_apply]

theorem mem_zagierSolutionGerms_of_trace {x : ℂ} (hx : x ∈ zagierPullbackRegularSet)
    {F W G : ℂ → ℂ} (hF : AnalyticAt ℂ F x)
    (hW : AnalyticAt ℂ W (mobiusAnalyticInvolution x))
    (hFo : zagierSecondOrderODE F =ᶠ[𝓝 x] 0)
    (hWo : zagierSecondOrderODE W =ᶠ[𝓝 (mobiusAnalyticInvolution x)] 0)
    (htrace : (G ∘ mobiusCoordinate) =ᶠ[𝓝 x]
      (fun z => F z + W (mobiusAnalyticInvolution z))) :
    (G : Germ (𝓝 (mobiusCoordinate x)) ℂ) ∈ zagierSolutionGerms (mobiusCoordinate x) := by
  have hx02 := mobiusCoordinate_regular_ne_zero_two hx.2
  have hw := mobiusAnalyticInvolution_mem_zagierPullbackRegularSet hx
  have hw02 := mobiusCoordinate_regular_ne_zero_two hw.2
  obtain ⟨L, hL, hLo, hLp⟩ :=
    exists_zagierAnalyticODE_of_secondOrder hx02.1 hx.1 hx02.2 hF hFo
  obtain ⟨R, hR, hRo, hRp⟩ :=
    exists_zagierAnalyticODE_of_secondOrder hw02.1 hw.1 hw02.2 hW hWo
  have hY := mobiusCoordinate_mobiusAnalyticInvolution hx.1
  rw [hY] at hR hRo
  have hRp' : (R ∘ mobiusCoordinate) =ᶠ[𝓝 x]
      (fun z => W (mobiusAnalyticInvolution z)) := by
    filter_upwards [hRp.comp_tendsto
      (analyticAt_mobiusAnalyticInvolution hx.1).continuousAt.tendsto,
      eventually_ne_nhds hx.1] with z hz hz1
    simpa only [Function.comp_apply, mobiusCoordinate_mobiusAnalyticInvolution hz1] using hz
  have hp : ((L + R) ∘ mobiusCoordinate) =ᶠ[𝓝 x]
      (fun z => F z + W (mobiusAnalyticInvolution z)) := hLp.add hRp'
  have he : G =ᶠ[𝓝 (mobiusCoordinate x)] L + R :=
    eventuallyEq_of_comp_of_analyticAt (analyticAt_mobiusCoordinate hx.1)
      (deriv_mobiusCoordinate_ne_zero hx02.1 hx.1 hx02.2) (htrace.trans hp.symm)
  rw [Germ.coe_eq.mpr he]
  change (L : Germ (𝓝 (mobiusCoordinate x)) ℂ) + R ∈ zagierSolutionGerms (mobiusCoordinate x)
  exact (zagierSolutionGerms (mobiusCoordinate x)).add_mem
    (mem_zagierSolutionGerms_iff.mpr ⟨hL, hLo⟩) (mem_zagierSolutionGerms_iff.mpr ⟨hR, hRo⟩)

/-- Branches returning to the same original point differ by a homogeneous fourth-order germ. -/
theorem ForcedHTraceContinuation.trace_sub_mem_solutionGerms
    {δ : C(unitInterval, zagierPullbackRegularSet)} {b c : ℂ}
    (C : ForcedHTraceContinuation δ b c) (s t : unitInterval) (hδ : δ s = δ t) :
    ((C.trace s - C.trace t : ℂ → ℂ) : Germ (𝓝 (mobiusCoordinate (δ t : ℂ))) ℂ) ∈
      zagierSolutionGerms (mobiusCoordinate (δ t : ℂ)) := by
  have hLs : AnalyticAt ℂ (C.left s) (δ t : ℂ) := by
    simpa only [hδ] using C.left_continuation.analytic s
  have hRs : AnalyticAt ℂ (C.right s) (mobiusAnalyticInvolution (δ t : ℂ)) := by
    simpa only [hδ] using C.right_continuation.analytic s
  have hLso := C.left_ode s
  have hRso := C.right_ode s
  rw [hδ] at hLso hRso
  have hLe : zagierSecondOrderODE (C.left s) =ᶠ[𝓝 (δ t : ℂ)]
      zagierSecondOrderODE (C.left t) := by
    filter_upwards [hLso, C.left_ode t] with z hs ht
    exact hs.trans ht.symm
  have hRe : zagierSecondOrderODE (C.right s) =ᶠ[𝓝 (mobiusAnalyticInvolution (δ t : ℂ))]
      zagierSecondOrderODE (C.right t) := by
    filter_upwards [hRso, C.right_ode t] with z hs ht
    exact hs.trans ht.symm
  apply mem_zagierSolutionGerms_of_trace (δ t).property
    (hLs.sub (C.left_continuation.analytic t)) (hRs.sub (C.right_continuation.analytic t))
    (eventually_zagierSecondOrderODE_sub_eq_zero hLs (C.left_continuation.analytic t) hLe)
    (eventually_zagierSecondOrderODE_sub_eq_zero hRs (C.right_continuation.analytic t) hRe)
  have hp := C.trace_pullback s
  rw [hδ] at hp
  filter_upwards [hp, C.trace_pullback t] with z hs ht
  dsimp only [Function.comp_apply, Pi.sub_apply] at hs ht ⊢
  rw [hs, ht]
  ring

/-- An actual continued G branch differs from the original sum by a homogeneous solution. -/
theorem exists_analyticContinuationAlong_gLinearCombination_loop (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ δ : C(unitInterval, zagierPullbackRegularSet),
      ‖(δ 0 : ℂ)‖ < R → δ 1 = δ 0 → ∃ G : unitInterval → ℂ → ℂ,
        AnalyticContinuationAlong (fun t => mobiusCoordinate (δ t : ℂ)) G ∧
        G 0 =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))] gLinearCombinationAnalytic a b c ∧
        ((G 1 - gLinearCombinationAnalytic a b c : ℂ → ℂ) :
          Germ (𝓝 (mobiusCoordinate (δ 0 : ℂ))) ℂ) ∈
            zagierSolutionGerms (mobiusCoordinate (δ 0 : ℂ)) := by
  obtain ⟨R, hR, hC⟩ := exists_forcedHTraceContinuation_gLinearCombination a b c hrel
  refine ⟨R, hR, ?_⟩
  intro δ hδ hloop
  obtain ⟨C, _, _, hg⟩ := hC δ hδ
  refine ⟨C.trace, C.trace_continuation, hg, ?_⟩
  have he : C.trace 1 - gLinearCombinationAnalytic a b c =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))]
      C.trace 1 - C.trace 0 := Filter.EventuallyEq.rfl.sub hg.symm
  rw [Germ.coe_eq.mpr he]
  exact C.trace_sub_mem_solutionGerms 1 0 hloop

end DirichletL

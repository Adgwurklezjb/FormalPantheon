import Analysis.AnalyticLinearODEContinuation

/-!
Full endpoint germs for contractible loops in an analytic matrix system.
This supplies pure-function invariance in CDT v2, Lemma `14functions`.
-/

namespace DirichletL.AnalyticMatrixODE

open Filter Topology Bundle
open scoped Topology Matrix

variable {I : Type*} [Fintype I] (D : AnalyticMatrixODE I)

theorem exists_analyticContinuationAlong_homotopic_refl {x : D.domain} (γ : Path x x)
    (hγ : γ.Homotopic (Path.refl x)) (f : ℂ → I → ℂ)
    (hf : AnalyticAt ℂ f (x : ℂ))
    (hfo : ∀ᶠ z in 𝓝 (x : ℂ), HasDerivAt f (D.matrix z *ᵥ f z) z) :
    ∃ F : unitInterval → ℂ → I → ℂ,
      (∀ i, AnalyticContinuationAlong (fun t => (γ t : ℂ)) (fun t z => F t z i)) ∧
      F 0 =ᶠ[𝓝 (x : ℂ)] f ∧ F 1 =ᶠ[𝓝 (x : ℂ)] f ∧
      ∀ t, ∀ᶠ z in 𝓝 (γ t : ℂ), HasDerivAt (F t) (D.matrix z *ᵥ F t z) z := by
  let p : D.Continuation x := ⟨x, D.solutionGermOfFun f hf hfo⟩
  let cov := D.isCoveringMap_continuationProjection x
  let u := cov.liftPath γ.toContinuousMap p γ.source
  have hp : ∀ t, (u t).proj = γ t :=
    fun t => congrFun (cov.liftPath_lifts γ.toContinuousMap p γ.source) t
  have hzero : u 0 = p := cov.liftPath_zero γ.toContinuousMap p γ.source
  have hc : (fun _ : unitInterval => p) =
      cov.liftPath (Path.refl x).toContinuousMap p rfl :=
    (cov.eq_liftPath_iff rfl).mpr ⟨continuous_const, rfl, rfl⟩
  have hone : u 1 = p :=
    (cov.liftPath_apply_one_eq_of_homotopicRel hγ p γ.source rfl).trans (congrFun hc.symm 1)
  choose F hFa hFo hFg using fun t => (u t).snd.property
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [hp] using
      D.analyticContinuationAlong_component x u.continuous (fun t => (hFg t).symm) i
  · have he := hFg 0
    rw [hzero] at he
    exact Germ.coe_eq.mp he
  · have he := hFg 1
    rw [hone] at he
    exact Germ.coe_eq.mp he
  · intro t
    simpa only [hp] using hFo t

theorem analyticContinuationAlong_end_eq_of_homotopic_refl {x : D.domain} (γ : Path x x)
    (hγ : γ.Homotopic (Path.refl x)) {f : ℂ → I → ℂ}
    (hf : AnalyticAt ℂ f (x : ℂ))
    (hfo : ∀ᶠ z in 𝓝 (x : ℂ), HasDerivAt f (D.matrix z *ᵥ f z) z)
    {F : unitInterval → ℂ → I → ℂ}
    (hF : ∀ i, AnalyticContinuationAlong (fun t => (γ t : ℂ)) (fun t z => F t z i))
    (hF0 : F 0 =ᶠ[𝓝 (x : ℂ)] f) : F 1 =ᶠ[𝓝 (x : ℂ)] f := by
  obtain ⟨G, hG, hG0, hG1, _⟩ := D.exists_analyticContinuationAlong_homotopic_refl γ hγ f hf hfo
  have hi (i : I) : (fun z => F 1 z i) =ᶠ[𝓝 (x : ℂ)] (fun z => G 1 z i) := by
    have he0 : (fun z => F 0 z i) =ᶠ[𝓝 (x : ℂ)] (fun z => G 0 z i) := by
      filter_upwards [hF0.trans hG0.symm] with z hz
      exact congrFun hz i
    simpa only [Path.target] using (hF i).eq_of_preconnectedSpace (hG i) (t₀ := 0)
      (by simpa only [Path.source] using he0) 1
  filter_upwards [eventually_all.mpr hi, hG1] with z hz hgz
  exact (funext hz).trans hgz

end DirichletL.AnalyticMatrixODE

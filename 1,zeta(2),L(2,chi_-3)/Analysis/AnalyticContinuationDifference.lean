import Analysis.AnalyticContinuationPaths

/-!
Full-germ subtraction and endpoint comparisons for the actual conjugate
continuations in CDT v2, Lemma `14functions` (TeX 8074-8100).
-/

namespace DirichletL.AnalyticContinuationAlong

open Filter unitInterval
open scoped Topology

theorem sub {T : Type*} [TopologicalSpace T] {γ : T → ℂ} {f g : T → ℂ → ℂ}
    (hf : AnalyticContinuationAlong γ f) (hg : AnalyticContinuationAlong γ g) :
    AnalyticContinuationAlong γ (fun t => f t - g t) := by
  refine ⟨hf.continuous, fun t => (hf.analytic t).sub (hg.analytic t), ?_⟩
  intro t
  filter_upwards [hf.locally_eq t, hg.locally_eq t] with s hfs hgs
  exact hfs.sub hgs

theorem trans_end_eq {X : Type*} [TopologicalSpace X] {x y z : X}
    (γ : Path x y) (δ : Path y z) (φ : X → ℂ) {F G H : I → ℂ → ℂ}
    (hF : AnalyticContinuationAlong (fun t => φ ((γ.trans δ) t)) F)
    (hG : AnalyticContinuationAlong (fun t => φ (γ t)) G)
    (hH : AnalyticContinuationAlong (fun t => φ (δ t)) H)
    (h0 : F 0 =ᶠ[𝓝 (φ x)] G 0) (hjoin : G 1 =ᶠ[𝓝 (φ y)] H 0) :
    F 1 =ᶠ[𝓝 (φ z)] H 1 := by
  obtain ⟨A, B, hA, hB, hA0, hB1, hAB, _, _⟩ :=
    exists_trans_parts γ δ φ hF (fun _ _ => True) (fun _ => trivial)
  have hAG : A 1 =ᶠ[𝓝 (φ y)] G 1 := by
    simpa only [Path.target] using hA.eq_of_preconnectedSpace hG (t₀ := 0)
      (by simpa only [Path.source, hA0] using h0) 1
  have hBH : B 0 =ᶠ[𝓝 (φ y)] H 0 := by
    simpa only [hAB] using hAG.trans hjoin
  simpa only [Path.target, hB1] using hB.eq_of_preconnectedSpace hH
    (t₀ := 0) (by simpa only [Path.source] using hBH) 1

theorem end_eq_of_conjugate {X : Type*} [TopologicalSpace X] {x y : X}
    (η : Path x y) (τ : Path y y) (φ : X → ℂ) {F G H : I → ℂ → ℂ}
    (hF : AnalyticContinuationAlong (fun t => φ (((η.trans τ).trans η.symm) t)) F)
    (hG : AnalyticContinuationAlong (fun t => φ (η t)) G)
    (hH : AnalyticContinuationAlong (fun t => φ (τ t)) H)
    (h0 : F 0 =ᶠ[𝓝 (φ x)] G 0) (hjoin : G 1 =ᶠ[𝓝 (φ y)] H 0)
    (hend : F 1 =ᶠ[𝓝 (φ x)] F 0) : H 1 =ᶠ[𝓝 (φ y)] H 0 := by
  obtain ⟨U, V, hU, hV, hU0, hV1, hUV, _, _⟩ :=
    exists_trans_parts (η.trans τ) η.symm φ hF (fun _ _ => True) (fun _ => trivial)
  have hUH : U 1 =ᶠ[𝓝 (φ y)] H 1 := trans_end_eq η τ φ hU hG hH
    (by simpa only [hU0] using h0) hjoin
  have hVr : AnalyticContinuationAlong (fun t => φ (η t)) (fun t => V (σ t)) := by
    simpa only [Function.comp_def, Path.symm_apply, unitInterval.symm_symm] using
      hV.reparam unitInterval.continuous_symm
  have hVr0 : (fun t => V (σ t)) 0 =ᶠ[𝓝 (φ (η 0))] G 0 := by
    simpa only [unitInterval.symm_zero, Path.source, hV1] using hend.trans h0
  have hVG : V 0 =ᶠ[𝓝 (φ y)] G 1 := by
    simpa only [unitInterval.symm_one, Path.target] using
      hVr.eq_of_preconnectedSpace hG hVr0 1
  exact hUH.symm.trans (by simpa only [hUV] using hVG.trans hjoin)

end DirichletL.AnalyticContinuationAlong

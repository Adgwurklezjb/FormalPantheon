import Analysis.ZagierEndpointInterval
import Analysis.ZagierSheetPaths

/-!
Retain the original regular paths as well as their projected paths for
CDT v2's coordinate `y in x` and Lemma `14functions` (TeX 8074-8100).
-/

namespace DirichletL

open Filter Set unitInterval
open scoped Topology

/-- The actual coordinate map between the two regular domains. -/
noncomputable def zagierPullbackProjection : C(zagierPullbackRegularSet, zagierODERegularSet) := {
  toFun x := ⟨mobiusCoordinate (x : ℂ), x.property.2⟩
  continuous_toFun := (continuous_iff_continuousAt.mpr (fun x =>
    (analyticAt_mobiusCoordinate x.property.1).continuousAt.comp
      continuous_subtype_val.continuousAt)).subtype_mk _ }

/-- Restrict an already regular original path to its regular subtype. -/
noncomputable def zagierPullbackPath {x y : ℂ} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ zagierPullbackRegularSet) :
    Path (⟨x, by simpa only [Path.source] using hγ 0⟩ : zagierPullbackRegularSet)
      ⟨y, by simpa only [Path.target] using hγ 1⟩ where
  toFun t := ⟨γ t, hγ t⟩
  continuous_toFun := γ.continuous.subtype_mk _
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

@[simp]
theorem zagierPullbackPath_apply {x y : ℂ} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ zagierPullbackRegularSet) (t : I) :
    (zagierPullbackPath γ hγ t : ℂ) = γ t := rfl

theorem zagierPullbackPath_projection {x y : ℂ} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ zagierPullbackRegularSet) :
    (zagierPullbackPath γ hγ).map zagierPullbackProjection.continuous =
      zagierMobiusPath γ (fun t => (hγ t).1) (fun t => (hγ t).2) := by
  apply Path.ext
  rfl

theorem zagierEndpointInterval_mem_pullback {r : ℝ} (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) :
    (r : ℂ) ∈ zagierPullbackRegularSet :=
  ⟨(zagierEndpointInterval_noncritical hr).2.1, mobiusCoordinate_regular_of_mem_Ioo hr⟩

/-- The fixed real interval connector in the original regular domain. -/
noncomputable def zagierPullbackIntervalPath {r s : ℝ}
    (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) (hs : s ∈ Ioo 0 (1 / 9 : ℝ)) :
    Path (⟨r, zagierEndpointInterval_mem_pullback hr⟩ : zagierPullbackRegularSet)
      ⟨s, zagierEndpointInterval_mem_pullback hs⟩ :=
  zagierPullbackPath ((zagierEndpointRealPath hr hs).map Complex.continuous_ofReal)
    (fun t => zagierEndpointInterval_mem_pullback (zagierEndpointRealPath_mem hr hs t))

theorem zagierPullbackIntervalPath_projection {r s : ℝ}
    (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) (hs : s ∈ Ioo 0 (1 / 9 : ℝ)) :
    (zagierPullbackIntervalPath hr hs).map zagierPullbackProjection.continuous =
      zagierEndpointPath hr hs := by
  apply Path.ext
  rfl

theorem norm_zagierPullbackIntervalPath_lt_one {r s : ℝ}
    (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) (hs : s ∈ Ioo 0 (1 / 9 : ℝ)) (t : I) :
    ‖(zagierPullbackIntervalPath hr hs t : ℂ)‖ < 1 := by
  change ‖((zagierEndpointRealPath hr hs t : ℝ) : ℂ)‖ < 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zagierEndpointRealPath_mem hr hs t).1]
  linarith [(zagierEndpointRealPath_mem hr hs t).2]

theorem mobiusGermPullback_zagierOriginalPathTransport (b : zagierODERegularSet)
    {x y : zagierPullbackRegularSet} (γ : Path x y) {F : I → ℂ → ℂ}
    (hF : AnalyticContinuationAlong (fun t => (γ t : ℂ)) F)
    (φ : zagierSolutionGerms (mobiusCoordinate (x : ℂ)))
    (hφ : mobiusGermPullback x.property.1
      (φ : Germ (𝓝 (mobiusCoordinate (x : ℂ))) ℂ) = F 0) :
    mobiusGermPullback y.property.1
      (zagierPathTransport b (γ.map zagierPullbackProjection.continuous) φ).val = F 1 := by
  let δ := γ.map continuous_subtype_val
  have he : γ.map zagierPullbackProjection.continuous =
      zagierMobiusPath δ (fun t => (γ t).property.1) (fun t => (γ t).property.2) := by
    apply Path.ext
    rfl
  rw [he]
  exact mobiusGermPullback_zagierPathTransport_of_analyticContinuation b δ _ _ _ _ hF φ hφ

end DirichletL

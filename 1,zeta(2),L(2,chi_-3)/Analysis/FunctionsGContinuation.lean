import Analysis.FunctionsGAnalytic
import Analysis.AnalyticContinuationChangeOfVariable

/-!
Continuation of the actual two-sheet trace in CDT v2, Definition `defG` and
Lemma `14functions`. Both original branches retain their forcing constants.
-/

namespace DirichletL

open Filter
open scoped Topology

theorem mem_hForcedRegularSet_of_mem_zagierPullbackRegularSet {x : ℂ}
    (hx : x ∈ zagierPullbackRegularSet) : x ∈ hForcedRegularSet := by
  apply (mem_hForcedRegularSet_iff x).mpr
  refine ⟨(mobiusCoordinate_regular_ne_zero_two hx.2).1, ?_, hx.1⟩
  intro hx9
  exact ((mem_zagierODERegularSet_iff _).mp hx.2).2.2.1
    (by rw [hx9, mobiusCoordinate_one_div_nine])

theorem mobiusAnalyticInvolution_mem_zagierPullbackRegularSet {x : ℂ}
    (hx : x ∈ zagierPullbackRegularSet) :
    mobiusAnalyticInvolution x ∈ zagierPullbackRegularSet :=
  ⟨mobiusAnalyticInvolution_ne_one hx.1, by
    simpa only [mobiusCoordinate_mobiusAnalyticInvolution hx.1] using hx.2⟩

/-- Two original forced continuations and their compatible analytic trace. -/
structure ForcedHTraceContinuation (δ : C(unitInterval, zagierPullbackRegularSet))
    (b c : ℂ) where
  /-- Representatives on the original sheet. -/
  left : unitInterval → ℂ → ℂ
  /-- Representatives on the involuted sheet. -/
  right : unitInterval → ℂ → ℂ
  /-- Representatives of the descended trace. -/
  trace : unitInterval → ℂ → ℂ
  left_continuation : AnalyticContinuationAlong (fun t => (δ t : ℂ)) left
  right_continuation :
    AnalyticContinuationAlong (fun t => mobiusAnalyticInvolution (δ t : ℂ)) right
  trace_continuation : AnalyticContinuationAlong (fun t => mobiusCoordinate (δ t : ℂ)) trace
  left_ode : ∀ t, ∀ᶠ z in 𝓝 (δ t : ℂ),
    zagierSecondOrderODE (left t) z = b + c / (1 - z)
  right_ode : ∀ t, ∀ᶠ z in 𝓝 (mobiusAnalyticInvolution (δ t : ℂ)),
    zagierSecondOrderODE (right t) z = b + c / (1 - z)
  trace_pullback : ∀ t, (trace t ∘ mobiusCoordinate) =ᶠ[𝓝 (δ t : ℂ)]
    (fun z => left t z + right t (mobiusAnalyticInvolution z))

theorem exists_forcedHTraceContinuation
    (δ : C(unitInterval, zagierPullbackRegularSet)) (f : ℂ → ℂ) (b c : ℂ)
    (hf : AnalyticAt ℂ f (δ 0 : ℂ))
    (hw : AnalyticAt ℂ f (mobiusAnalyticInvolution (δ 0 : ℂ)))
    (hfo : ∀ᶠ z in 𝓝 (δ 0 : ℂ), zagierSecondOrderODE f z = b + c / (1 - z))
    (hwo : ∀ᶠ z in 𝓝 (mobiusAnalyticInvolution (δ 0 : ℂ)),
      zagierSecondOrderODE f z = b + c / (1 - z)) :
    ∃ C : ForcedHTraceContinuation δ b c,
      C.left 0 =ᶠ[𝓝 (δ 0 : ℂ)] f ∧
      C.right 0 =ᶠ[𝓝 (mobiusAnalyticInvolution (δ 0 : ℂ))] f := by
  let leftPath : C(unitInterval, hForcedRegularSet) :=
    ⟨fun t => ⟨(δ t : ℂ), mem_hForcedRegularSet_of_mem_zagierPullbackRegularSet (δ t).property⟩,
      (continuous_subtype_val.comp δ.continuous).subtype_mk _⟩
  have hi : Continuous (fun t => mobiusAnalyticInvolution (δ t : ℂ)) :=
    continuous_iff_continuousAt.mpr fun t =>
      (analyticAt_mobiusAnalyticInvolution (δ t).property.1).continuousAt.comp
        (f := fun s => (δ s : ℂ))
        (continuous_subtype_val.comp δ.continuous).continuousAt
  let rightPath : C(unitInterval, hForcedRegularSet) :=
    ⟨fun t => ⟨mobiusAnalyticInvolution (δ t : ℂ),
      mem_hForcedRegularSet_of_mem_zagierPullbackRegularSet
        (mobiusAnalyticInvolution_mem_zagierPullbackRegularSet (δ t).property)⟩,
      hi.subtype_mk _⟩
  obtain ⟨F, hF, hF0, hFo⟩ := exists_analyticContinuationAlong_forcedH leftPath f b c hf hfo
  obtain ⟨W, hW, hW0, hWo⟩ := exists_analyticContinuationAlong_forcedH rightPath f b c hw hwo
  have hW' : AnalyticContinuationAlong (fun t => (δ t : ℂ))
      (fun t z => W t (mobiusAnalyticInvolution z)) :=
    hW.comp (continuous_subtype_val.comp δ.continuous)
      (fun t => analyticAt_mobiusAnalyticInvolution (δ t).property.1) (fun _ => rfl)
  obtain ⟨G, hG, hGp⟩ := (hF.add hW').exists_of_comp
    (fun t => analyticAt_mobiusCoordinate (δ t).property.1)
    (fun t => deriv_mobiusCoordinate_ne_zero
      (mobiusCoordinate_regular_ne_zero_two (δ t).property.2).1 (δ t).property.1
      (mobiusCoordinate_regular_ne_zero_two (δ t).property.2).2)
  exact ⟨{
    left := F
    right := W
    trace := G
    left_continuation := hF
    right_continuation := hW
    trace_continuation := hG
    left_ode := hFo
    right_ode := hWo
    trace_pullback := hGp }, hF0, hW0⟩

theorem ForcedHTraceContinuation.initial_trace_eq
    {δ : C(unitInterval, zagierPullbackRegularSet)} {b c : ℂ}
    (C : ForcedHTraceContinuation δ b c) {f g : ℂ → ℂ}
    (hl : C.left 0 =ᶠ[𝓝 (δ 0 : ℂ)] f)
    (hr : C.right 0 =ᶠ[𝓝 (mobiusAnalyticInvolution (δ 0 : ℂ))] f)
    (hg : (g ∘ mobiusCoordinate) =ᶠ[𝓝 (δ 0 : ℂ)]
      (fun z => f z + f (mobiusAnalyticInvolution z))) :
    C.trace 0 =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))] g := by
  have hx := mobiusCoordinate_regular_ne_zero_two (δ 0).property.2
  apply eventuallyEq_of_comp_of_analyticAt (analyticAt_mobiusCoordinate (δ 0).property.1)
    (deriv_mobiusCoordinate_ne_zero hx.1 (δ 0).property.1 hx.2)
  exact (C.trace_pullback 0).trans ((hl.add (hr.comp_tendsto
    (analyticAt_mobiusAnalyticInvolution (δ 0).property.1).continuousAt.tendsto)).trans hg.symm)

/-- The literal combined H and G sums give actual initial data on every sufficiently small path. -/
theorem exists_forcedHTraceContinuation_gLinearCombination (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ δ : C(unitInterval, zagierPullbackRegularSet), ‖(δ 0 : ℂ)‖ < R →
      ∃ C : ForcedHTraceContinuation δ (b : ℂ) (c : ℂ),
        C.left 0 =ᶠ[𝓝 (δ 0 : ℂ)] hLinearCombinationAnalytic a b c ∧
        C.right 0 =ᶠ[𝓝 (mobiusAnalyticInvolution (δ 0 : ℂ))] hLinearCombinationAnalytic a b c ∧
        C.trace 0 =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))] gLinearCombinationAnalytic a b c := by
  obtain ⟨R, hR, hinit⟩ := exists_gLinearCombination_initial_radius a b c hrel
  refine ⟨R, hR, ?_⟩
  intro δ hδ
  obtain ⟨hx, hw, _, hgp, _⟩ := hinit (δ 0 : ℂ) hδ
  have hfo {x : ℂ} (hx : ‖x‖ < 1) : ∀ᶠ z in 𝓝 x,
      zagierSecondOrderODE (hLinearCombinationAnalytic a b c) z = (b : ℂ) + (c : ℂ) / (1 - z) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with z hz
    exact hLinearCombinationAnalytic_ode a b c hrel hz
  obtain ⟨C, hl, hr⟩ := exists_forcedHTraceContinuation δ (hLinearCombinationAnalytic a b c) b c
    (analyticAt_hLinearCombinationAnalytic a b c hrel hx)
    (analyticAt_hLinearCombinationAnalytic a b c hrel hw) (hfo hx) (hfo hw)
  exact ⟨C, hl, hr, C.initial_trace_eq hl hr hgp⟩

end DirichletL

import Analysis.FunctionsGPrimitiveCompanion

/-!
Actual simultaneous continuation of G and its three normalized primitives,
as used in CDT v2, Lemma `14functions`. The original constants G(0), G'(0)
remain fixed when the trace and primitive branches are continued.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

/-- Compatible trace and primitive branches with the original subtraction constants. -/
structure GPrimitiveContinuation (δ : C(unitInterval, zagierPullbackRegularSet))
    (k0 k1 : ℂ) where
  /-- Local representatives of the continued two-sheet trace. -/
  trace : unitInterval → ℂ → ℂ
  /-- Local representatives of the three continued normalized primitives. -/
  primitive : Fin 3 → unitInterval → ℂ → ℂ
  trace_continuation : AnalyticContinuationAlong (fun t => mobiusCoordinate (δ t : ℂ)) trace
  primitive_continuation : ∀ j,
    AnalyticContinuationAlong (fun t => mobiusCoordinate (δ t : ℂ)) (primitive j)
  primitive_deriv : ∀ j t, deriv (primitive j t) =ᶠ[𝓝 (mobiusCoordinate (δ t : ℂ))]
    gPrimitiveIntegrand (trace t) k0 k1 j

/-- The matrix covering continues the actual vector and preserves all its initial germs. -/
theorem exists_gPrimitiveContinuation_of_matrix
    (δ : C(unitInterval, zagierPullbackRegularSet)) (b c k0 k1 : ℂ)
    (f G : ℂ → ℂ) (J : Fin 3 → ℂ → ℂ)
    (hs : AnalyticAt ℂ (gPrimitiveState f J) (δ 0 : ℂ))
    (hso : ∀ᶠ x in 𝓝 (δ 0 : ℂ), HasDerivAt (gPrimitiveState f J)
      (gPrimitiveMatrix b c k0 k1 x *ᵥ gPrimitiveState f J x) x)
    (htrace : (G ∘ mobiusCoordinate) =ᶠ[𝓝 (δ 0 : ℂ)]
      (fun x => f x + f (mobiusAnalyticInvolution x))) :
    ∃ C : GPrimitiveContinuation δ k0 k1,
      C.trace 0 =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))] G ∧
      ∀ j, C.primitive j 0 =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))] J j := by
  obtain ⟨V, hV, hinit, hVo⟩ := (gPrimitiveSystem b c k0 k1).exists_analyticContinuationAlong
    δ (gPrimitiveState f J) hs hso
  have hY (t : unitInterval) := analyticAt_mobiusCoordinate (δ t).property.1
  have hne (t : unitInterval) := deriv_mobiusCoordinate_ne_zero
    (mobiusCoordinate_regular_ne_zero_two (δ t).property.2).1 (δ t).property.1
    (mobiusCoordinate_regular_ne_zero_two (δ t).property.2).2
  have he : ∀ t, (fun x => V t x 4) =ᶠ[𝓝 (δ t : ℂ)] fun _ => (1 : ℂ) := by
    apply (hV 4).eq_of_preconnectedSpace
      (AnalyticContinuationAlong.const (continuous_subtype_val.comp δ.continuous)
        (fun _ => analyticAt_const)) (t₀ := 0)
    filter_upwards [hinit] with x hx
    exact congrFun hx (4 : Fin 8)
  obtain ⟨T, hT, hTp⟩ := ((hV 0).add (hV 2)).exists_of_comp hY hne
  choose P hP hPp using fun j : Fin 3 => (hV (Fin.natAdd 5 j)).exists_of_comp hY hne
  have hPd (j : Fin 3) (t : unitInterval) :
      deriv (P j t) =ᶠ[𝓝 (mobiusCoordinate (δ t : ℂ))] gPrimitiveIntegrand (T t) k0 k1 j := by
    apply eventuallyEq_of_comp_of_analyticAt (hY t) (hne t)
    have hPa := (hY t).continuousAt.tendsto.eventually ((hP j).analytic t).eventually_analyticAt
    filter_upwards [hVo t, (hPp j t).deriv, hTp t, he t, hPa,
      isOpen_zagierPullbackRegularSet.mem_nhds (δ t).property]
      with x hvo hpd ht he1 hpx hx
    have hn := deriv_mobiusCoordinate_ne_zero
      (mobiusCoordinate_regular_ne_zero_two hx.2).1 hx.1
      (mobiusCoordinate_regular_ne_zero_two hx.2).2
    have hprod := (hpx.differentiableAt.hasDerivAt.comp x
      (analyticAt_mobiusCoordinate hx.1).differentiableAt.hasDerivAt).deriv
    have hvp := (hasDerivAt_pi.mp hvo (Fin.natAdd 5 j)).deriv
    change deriv (fun w => V t w (Fin.natAdd 5 j)) x =
      (gPrimitiveMatrix b c k0 k1 x *ᵥ V t x) (Fin.natAdd 5 j) at hvp
    rw [gPrimitiveMatrix_mulVec_integrals] at hvp
    simp only [he1, mul_one] at hvp
    change deriv (P j t) (mobiusCoordinate x) =
      gPrimitiveIntegrand (T t) k0 k1 j (mobiusCoordinate x)
    apply mul_left_cancel₀ hn
    calc
      deriv mobiusCoordinate x * deriv (P j t) (mobiusCoordinate x) =
          deriv (P j t ∘ mobiusCoordinate) x := by simpa only [mul_comm] using hprod.symm
      _ = deriv (fun w => V t w (Fin.natAdd 5 j)) x := hpd
      _ = deriv mobiusCoordinate x *
          gPrimitiveIntegrand (fun _ => V t x 0 + V t x 2) k0 k1 j (mobiusCoordinate x) := hvp
      _ = deriv mobiusCoordinate x * gPrimitiveIntegrand (T t) k0 k1 j
          (mobiusCoordinate x) := by
        change T t (mobiusCoordinate x) = V t x 0 + V t x 2 at ht
        fin_cases j <;> simp [gPrimitiveIntegrand, ht]
  refine ⟨{
    trace := T
    primitive := P
    trace_continuation := hT
    primitive_continuation := hP
    primitive_deriv := hPd }, ?_, ?_⟩
  · apply eventuallyEq_of_comp_of_analyticAt (hY 0) (hne 0)
    apply (hTp 0).trans
    apply Filter.EventuallyEq.trans _ htrace.symm
    filter_upwards [hinit] with x hx
    rw [hx]
    rfl
  · intro j
    apply eventuallyEq_of_comp_of_analyticAt (hY 0) (hne 0)
    apply (hPp j 0).trans
    filter_upwards [hinit] with x hx
    simpa only [gPrimitiveState_integrals] using congrFun hx (Fin.natAdd 5 j)

/-- The actual rational G combination and its literal normalized primitives continue together. -/
theorem exists_gPrimitiveContinuation_gLinearCombination (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ δ : C(unitInterval, zagierPullbackRegularSet),
      ‖(δ 0 : ℂ)‖ < R →
      ∃ C : GPrimitiveContinuation δ (gLinearCombinationAnalytic a b c 0)
          (deriv (gLinearCombinationAnalytic a b c) 0),
        C.trace 0 =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))] gLinearCombinationAnalytic a b c ∧
        ∀ j : Fin 3, C.primitive j 0 =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))]
          zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC))
            (j.castAdd 4) := by
  obtain ⟨R, hR, hinit⟩ := exists_gPrimitives_initial_radius a b c hrel
  refine ⟨R, hR, ?_⟩
  intro δ hδ
  let f := hLinearCombinationAnalytic a b c
  let G := gLinearCombinationAnalytic a b c
  let J : Fin 3 → ℂ → ℂ := fun j =>
    zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC)) (j.castAdd 4)
  obtain ⟨hx1, hw1, hJ, he, _, _⟩ := hinit (δ 0 : ℂ) hδ
  have hs : AnalyticAt ℂ (gPrimitiveState f J) (δ 0 : ℂ) :=
    analyticAt_gPrimitiveState (δ 0).property.1
      (analyticAt_hLinearCombinationAnalytic a b c hrel hx1)
      (analyticAt_hLinearCombinationAnalytic a b c hrel hw1) (fun j => hJ (j.castAdd 4))
  have hso : ∀ᶠ x in 𝓝 (δ 0 : ℂ), HasDerivAt (gPrimitiveState f J)
      (gPrimitiveMatrix (b : ℂ) (c : ℂ) (G 0) (deriv G 0) x *ᵥ gPrimitiveState f J x) x := by
    filter_upwards [continuousAt_id.norm.eventually_lt_const hδ,
      isOpen_zagierPullbackRegularSet.mem_nhds (δ 0).property] with x hxr hx
    obtain ⟨hx1, hw1, _, he, hd, _⟩ := hinit x hxr
    exact hasDerivAt_gPrimitiveState_of_ode hx
      (analyticAt_hLinearCombinationAnalytic a b c hrel hx1)
      (analyticAt_hLinearCombinationAnalytic a b c hrel hw1)
      (hLinearCombinationAnalytic_ode a b c hrel hx1)
      (hLinearCombinationAnalytic_ode a b c hrel hw1) he.eq_of_nhds
      (fun j => hd j (mobiusCoordinate_regular_ne_zero_two hx.2).1)
  exact exists_gPrimitiveContinuation_of_matrix δ (b : ℂ) (c : ℂ) (G 0) (deriv G 0)
    f G J hs hso he

namespace GPrimitiveContinuation

variable {δ : C(unitInterval, zagierPullbackRegularSet)} {k0 k1 : ℂ}
    (C : GPrimitiveContinuation δ k0 k1)

/-- All seven continued functions in the same order as the initial Zagier family. -/
noncomputable def functions : Fin 7 → unitInterval → ℂ → ℂ :=
  ![C.primitive 0, C.primitive 1, C.primitive 2, C.trace,
    fun t => deriv (C.trace t), fun t => deriv (deriv (C.trace t)),
    fun t => deriv (deriv (deriv (C.trace t)))]

theorem functions_continuation (i : Fin 7) :
    AnalyticContinuationAlong (fun t => mobiusCoordinate (δ t : ℂ)) (C.functions i) := by
  fin_cases i
  · exact C.primitive_continuation 0
  · exact C.primitive_continuation 1
  · exact C.primitive_continuation 2
  · exact C.trace_continuation
  · exact C.trace_continuation.deriv
  · exact C.trace_continuation.deriv.deriv
  · exact C.trace_continuation.deriv.deriv.deriv

theorem functions_initial {F : PowerSeries ℚ}
    (hG : C.trace 0 =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))] (complexSeries F).sum)
    (hP : ∀ j : Fin 3, C.primitive j 0 =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))]
      zagierAuxiliaryFunctions F (j.castAdd 4)) (i : Fin 7) :
    C.functions i 0 =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))] zagierAuxiliaryFunctions F i := by
  fin_cases i
  · exact hP 0
  · exact hP 1
  · exact hP 2
  · exact hG
  · exact hG.deriv
  · exact hG.deriv.deriv
  · exact hG.deriv.deriv.deriv

end GPrimitiveContinuation

end DirichletL

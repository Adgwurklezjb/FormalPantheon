import Analysis.AnalyticContinuationRelations
import Analysis.FunctionsGDifferenceFamily
import Analysis.FunctionsGSelectedMonodromy

/-!
The fourteen-function independence of CDT v2, Lemma `14functions`
(supplied TeX 8044-8115), under the normalized nonzero rational relation.
The scalar action on punctured germs is given by rational evaluation.
-/

namespace DirichletL

open Filter Set
open scoped Topology

/-- The literal fourteen functions in CDT v2, `14functions`. -/
noncomputable def cdtFourteenFamily (a b c : ℚ) : Fin 14 → ℂ → ℂ :=
  Fin.append (zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC)))
    pureSevenDescentFamily

theorem eq_zero_of_cdtFourteenPolynomialRelation (a b c : ℚ)
    (hnum : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) (P : Fin 14 → Polynomial ℂ)
    (hrel : (fun z => ∑ i, (P i).eval z * cdtFourteenFamily a b c i z) =ᶠ[𝓝[≠] (0 : ℂ)] 0) :
    P = 0 := by
  obtain ⟨ε, hε, hnear⟩ := exists_radius_eventuallyEq_zero_of_punctured hrel
  obtain ⟨p, hp, _, hpY, δ, C, hC0, hCne, hCo, hCd, B, hBcont, hB0, hB1, _⟩ :=
    exists_gLinearCombination_pure_invariant_monodromy a b c hnum hne hε
  let y := mobiusCoordinate (p : ℂ)
  let A := zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC))
  have hy0 : y ≠ 0 := ((mem_zagierODERegularSet_iff _).mp
    (mobiusCoordinate_regular_of_mem_Ioo hp)).1
  have hstart : (fun z => ∑ i, (P i).eval z * cdtFourteenFamily a b c i z) =ᶠ[𝓝 y] 0 :=
    hnear y (by simpa only [dist_zero_right] using hpY) hy0
  have hδ0 : (δ.toContinuousMap 0 : ℂ) = (p : ℂ) := congrArg Subtype.val δ.source
  have hδ1 : (δ.toContinuousMap 1 : ℂ) = (p : ℂ) := congrArg Subtype.val δ.target
  have hδloop : δ.toContinuousMap 1 = δ.toContinuousMap 0 := δ.target.trans δ.source.symm
  let W : Fin 14 → unitInterval → ℂ → ℂ := Fin.append C.functions (fun i t z => B t z i)
  have hW (i : Fin 14) : AnalyticContinuationAlong
      (fun t => mobiusCoordinate (δ t : ℂ)) (W i) := by
    refine Fin.addCases (m := 7) (n := 7) ?_ ?_ i
    · intro j
      simpa only [W, Fin.append_left] using C.functions_continuation j
    · intro j
      simpa only [W, Fin.append_right] using hBcont j
  have hW0 (i : Fin 14) : W i 0 =ᶠ[𝓝 y] cdtFourteenFamily a b c i := by
    refine Fin.addCases (m := 7) (n := 7) ?_ ?_ i
    · intro j
      simpa only [W, cdtFourteenFamily, Fin.append_left] using hC0 j
    · intro j
      filter_upwards [hB0] with z hz
      simpa only [W, cdtFourteenFamily, Fin.append_right] using
        (congrFun hz j).trans (pureSevenState_apply z j)
  have hWstart : (fun z => ∑ i, (P i).eval z * W i 0 z) =ᶠ[𝓝 y] 0 := by
    filter_upwards [hstart, eventually_all.mpr hW0] with z hz hw
    simpa only [hw] using hz
  have hend : (fun z => ∑ i, (P i).eval z * W i 1 z) =ᶠ[𝓝 y] 0 := by
    simpa only [hδ1] using AnalyticContinuationAlong.polynomial_relation
      C.trace_continuation.continuous P hW (t0 := 0)
      (by simpa only [hδ0] using hWstart) 1
  have hdiffrel : (fun z => ∑ i : Fin 7,
      (P (i.castAdd 7)).eval z * (C.functions i 1 z - A i z)) =ᶠ[𝓝 y] 0 := by
    filter_upwards [hend, hstart, hB1] with z he hs hb
    rw [Fin.sum_univ_add (a := 7) (b := 7)] at he hs
    simp only [W, cdtFourteenFamily, Fin.append_left, Fin.append_right] at he hs
    have hBz (i : Fin 7) : B 1 z i = pureSevenDescentFamily i z :=
      (congrFun hb i).trans (pureSevenState_apply z i)
    simp only [hBz] at he
    simp only [mul_sub, Finset.sum_sub_distrib]
    change (∑ i : Fin 7, (P (i.castAdd 7)).eval z * C.functions i 1 z) -
      (∑ i : Fin 7, (P (i.castAdd 7)).eval z *
        zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC)) i z) = 0
    linear_combination he - hs
  let D := C.trace 1 - gLinearCombinationAnalytic a b c
  let J : Fin 3 → ℂ → ℂ := fun j => C.primitive j 1 - A (j.castAdd 4)
  let φ : zagierSolutionGerms y := ⟨(D : Germ (𝓝 y) ℂ), hCo⟩
  have hφ : φ ≠ 0 := by
    intro h
    have hz : D =ᶠ[𝓝 y] 0 := Germ.coe_eq.mp (congrArg Subtype.val h)
    apply hCne
    filter_upwards [hz] with z hz
    exact sub_eq_zero.mp hz
  have hJ (j : Fin 3) : ∀ᶠ z in 𝓝[≠] y, HasDerivAt (J j) (D z / z ^ (j : ℕ)) z := by
    have hpa : AnalyticAt ℂ (C.primitive j 1) y := by
      simpa only [hδ1] using (C.primitive_continuation j).analytic 1
    have haa : AnalyticAt ℂ (A (j.castAdd 4)) y := by
      have hca : AnalyticAt ℂ (C.functions (j.castAdd 4) 0) y := by
        simpa only [hδ0] using (C.functions_continuation (j.castAdd 4)).analytic 0
      exact hca.congr (hC0 (j.castAdd 4))
    have hja : AnalyticAt ℂ (J j) y := hpa.sub haa
    filter_upwards [hja.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      (hCd j).filter_mono nhdsWithin_le_nhds] with z ha hd
    have hd' : deriv (J j) z = D z / z ^ (j : ℕ) := hd
    rw [← hd']
    exact ha.differentiableAt.hasDerivAt
  have hfamily (i : Fin 7) : (C.functions i 1 - A i) =ᶠ[𝓝 y]
      zagierHomogeneousPrimitiveFamily D J i := by
    simpa only [hδ0] using C.functions_sub_initial hδloop
      (fun j => by simpa only [hδ0] using hC0 j) i
  let U : Fin 7 → RatFunc ℂ := fun i => algebraMap (Polynomial ℂ) (RatFunc ℂ) (P (i.castAdd 7))
  have hU : U = 0 := eq_zero_of_zagierHomogeneousFamilyRelation hp U hφ rfl J hJ (by
    filter_upwards [hdiffrel.filter_mono nhdsWithin_le_nhds,
      (eventually_all.mpr hfamily).filter_mono nhdsWithin_le_nhds] with z hz hf
    have he (i : Fin 7) : (U i).eval (RingHom.id ℂ) z = (P (i.castAdd 7)).eval z := by
      simp only [U, RatFunc.eval_algebraMap, Algebra.algebraMap_self_apply, Polynomial.eval₂_id]
    simpa only [he, ← hf, Pi.sub_apply] using hz)
  have hPG (i : Fin 7) : P (i.castAdd 7) = 0 := by
    apply RatFunc.algebraMap_injective ℂ
    simpa only [map_zero] using congrFun hU i
  let V : Fin 7 → RatFunc ℂ := fun i => algebraMap (Polynomial ℂ) (RatFunc ℂ) (P (i.natAdd 7))
  have hV : V = 0 := eq_zero_of_pureSevenDescentFamilyRelation V (by
    filter_upwards [hrel] with z hz
    rw [Fin.sum_univ_add (a := 7) (b := 7)] at hz
    simp only [cdtFourteenFamily, Fin.append_left, Fin.append_right,
      hPG, Polynomial.eval_zero, zero_mul, Finset.sum_const_zero, zero_add] at hz
    simpa only [V, RatFunc.eval_algebraMap, Algebra.algebraMap_self_apply, Polynomial.eval₂_id]
      using hz)
  funext i
  refine Fin.addCases (m := 7) (n := 7) hPG ?_ i
  intro j
  apply RatFunc.algebraMap_injective ℂ
  simpa only [Pi.zero_apply, map_zero] using congrFun hV j

theorem eq_zero_of_cdtFourteenRatFuncRelation (a b c : ℚ)
    (hnum : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) (C : Fin 14 → RatFunc ℂ)
    (hrel : (fun z => ∑ i, (C i).eval (RingHom.id ℂ) z * cdtFourteenFamily a b c i z)
      =ᶠ[𝓝[≠] (0 : ℂ)] 0) : C = 0 := by
  obtain ⟨Q, hQ, P, hP⟩ := exists_ratFunc_denominator C
  have hG (p : Polynomial ℂ) : ratFuncEvalGerm 0
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) = (fun z => p.eval z : ℂ → ℂ) := by
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall (fun z => by simp only [RatFunc.eval_algebraMap, Algebra.algebraMap_self_apply, Polynomial.eval₂_id])
  have heval (i : Fin 14) : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      (P i).eval z = Q.eval z * (C i).eval (RingHom.id ℂ) z := by
    apply Germ.coe_eq.mp
    have he := congrArg (ratFuncEvalGerm 0) (hP i)
    simpa only [map_mul (ratFuncEvalGerm 0), hG] using he
  have hclear : (fun z => ∑ i, (P i).eval z * cdtFourteenFamily a b c i z)
      =ᶠ[𝓝[≠] (0 : ℂ)] 0 := by
    filter_upwards [hrel, eventually_all.mpr heval] with z hz he
    simp only [he, mul_assoc, ← Finset.mul_sum, hz, mul_zero, Pi.zero_apply]
  have hPzero := eq_zero_of_cdtFourteenPolynomialRelation a b c hnum hne P hclear
  funext i
  have he : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q * C i = 0 := by
    rw [← hP i, show P i = 0 from congrFun hPzero i, map_zero]
  exact (mul_eq_zero.mp he).resolve_left (RatFunc.algebraMap_ne_zero hQ)

/-- Rational independence acts on punctured germs through rational evaluation. -/
theorem linearIndependent_cdtFourteenFamily (a b c : ℚ)
    (hnum : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    letI := (ratFuncEvalGerm 0).toModule
    LinearIndependent (RatFunc ℂ)
      (fun i : Fin 14 => (cdtFourteenFamily a b c i : Germ (𝓝[≠] (0 : ℂ)) ℂ)) := by
  letI := (ratFuncEvalGerm 0).toModule
  apply Fintype.linearIndependent_iff.mpr
  intro C hC i
  change ∑ k, ratFuncEvalGerm 0 (C k) *
    (cdtFourteenFamily a b c k : Germ (𝓝[≠] (0 : ℂ)) ℂ) = 0 at hC
  have he : ((fun z => ∑ k, (C k).eval (RingHom.id ℂ) z * cdtFourteenFamily a b c k z) :
      Germ (𝓝[≠] (0 : ℂ)) ℂ) =
      ∑ k, ratFuncEvalGerm 0 (C k) *
        (cdtFourteenFamily a b c k : Germ (𝓝[≠] (0 : ℂ)) ℂ) := by
    rw [show (fun z => ∑ k, (C k).eval (RingHom.id ℂ) z * cdtFourteenFamily a b c k z) =
        ∑ k, (fun z => (C k).eval (RingHom.id ℂ) z * cdtFourteenFamily a b c k z) by
      funext z
      simp only [Finset.sum_apply]]
    rw [Germ.coe_sum]
    rfl
  exact congrFun (eq_zero_of_cdtFourteenRatFuncRelation a b c hnum hne C
    (Germ.coe_eq.mp (he.trans hC))) i

end DirichletL

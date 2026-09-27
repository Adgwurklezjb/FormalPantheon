import Analysis.FunctionsHSelectedMonodromy
import Analysis.FunctionsGTraceNonzero
import Analysis.PureFunctionMonodromy

/-!
Simultaneous actual monodromy for CDT v2, Lemma `14functions` (TeX 8074-8100):
the seven pure germs return unchanged, while the G trace has a nonzero
homogeneous difference and its normalized primitives have the required
difference derivatives. All continuations use the same projected path.
-/

namespace DirichletL

open Filter Set unitInterval
open scoped Topology Matrix

theorem exists_gLinearCombination_pure_invariant_monodromy (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ, ∃ hp : p ∈ Ioo 0 (1 / 9 : ℝ), p < ε ∧ ‖mobiusCoordinate (p : ℂ)‖ < ε ∧
      ∃ δ : Path (⟨p, zagierEndpointInterval_mem_pullback hp⟩ : zagierPullbackRegularSet)
          ⟨p, zagierEndpointInterval_mem_pullback hp⟩,
      ∃ C : GPrimitiveContinuation δ.toContinuousMap (gLinearCombinationAnalytic a b c 0)
          (deriv (gLinearCombinationAnalytic a b c) 0),
        (∀ i : Fin 7, C.functions i 0 =ᶠ[𝓝 (mobiusCoordinate (p : ℂ))]
          zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC)) i) ∧
        (¬C.trace 1 =ᶠ[𝓝 (mobiusCoordinate (p : ℂ))] gLinearCombinationAnalytic a b c) ∧
        ((C.trace 1 - gLinearCombinationAnalytic a b c : ℂ → ℂ) :
          Germ (𝓝 (mobiusCoordinate (p : ℂ))) ℂ) ∈
            zagierSolutionGerms (mobiusCoordinate (p : ℂ)) ∧
        (∀ j : Fin 3, deriv (C.primitive j 1 -
          zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC))
            (j.castAdd 4)) =ᶠ[𝓝 (mobiusCoordinate (p : ℂ))]
          (fun y => (C.trace 1 y - gLinearCombinationAnalytic a b c y) / y ^ (j : ℕ))) ∧
        ∃ B : I → ℂ → Fin 7 → ℂ,
          (∀ i, AnalyticContinuationAlong (fun t => mobiusCoordinate (δ t : ℂ))
            (fun t z => B t z i)) ∧
          B 0 =ᶠ[𝓝 (mobiusCoordinate (p : ℂ))] pureSevenState ∧
          B 1 =ᶠ[𝓝 (mobiusCoordinate (p : ℂ))] pureSevenState ∧
          ∀ t, ∀ᶠ z in 𝓝 (mobiusCoordinate (δ t : ℂ)),
            HasDerivAt (B t) (pureSevenMatrix z *ᵥ B t z) z := by
  obtain ⟨R, hR, hG⟩ := exists_gPrimitiveContinuation_nontrivial_of_H_loop a b c hrel
  obtain ⟨P, hP, hPure⟩ := exists_analyticContinuationAlong_pureSeven_homotopic_refl
  obtain ⟨S, hS, hnull⟩ := exists_zagierEndpointCircle_pure_conjugate_homotopic_refl
  have hY : ContinuousAt (fun s : ℝ => mobiusCoordinate (s : ℂ)) 0 :=
    (analyticAt_mobiusCoordinate (by norm_num : ((0 : ℝ) : ℂ) ≠ 1)).continuousAt.comp
      (f := fun s : ℝ => (s : ℂ)) Complex.continuous_ofReal.continuousAt
  have hY0 : ‖mobiusCoordinate ((0 : ℝ) : ℂ)‖ < min P ε := by
    simpa [mobiusCoordinate] using lt_min hP hε
  obtain ⟨d, hd, hsmall⟩ := Metric.mem_nhds_iff.mp (hY.norm.eventually_lt_const hY0)
  obtain ⟨p, hp0, hplt⟩ := exists_between
    (lt_min (lt_min hR (by norm_num : (0 : ℝ) < 1 / 9)) (lt_min hd hε))
  have hpR : p < R := hplt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hp9 : p < 1 / 9 := hplt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hpd : p < d := hplt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hpε : p < ε := hplt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hp : p ∈ Ioo 0 (1 / 9 : ℝ) := ⟨hp0, hp9⟩
  have hpY : ‖mobiusCoordinate (p : ℂ)‖ < min P ε :=
    hsmall (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hp0] using hpd)
  obtain ⟨q, hq, r, hr, hrS, _, τ, hτ, η, F, hF, hF0, _, hFne⟩ :=
    exists_hLinearCombination_endpoint_conjugate a b c hrel hne hp hS
  let δ := (η.trans τ).trans η.symm
  have hδ0 : (δ.toContinuousMap 0 : ℂ) = (p : ℂ) := congrArg Subtype.val δ.source
  have hδloop : δ.toContinuousMap 1 = δ.toContinuousMap 0 := δ.target.trans δ.source.symm
  have hpRn : ‖(p : ℂ)‖ < R := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0] using hpR
  obtain ⟨C, hC0, hCne, hCo, hCd⟩ := hG δ.toContinuousMap
    (by simpa only [hδ0] using hpRn) hδloop F hF
    (by simpa only [hδ0] using hF0) (by simpa only [hδ0] using hFne)
  have hprojection : δ.map zagierPullbackProjection.continuous =
      (((η.map zagierPullbackProjection.continuous).trans
        (τ.map zagierPullbackProjection.continuous)).trans
          (η.map zagierPullbackProjection.continuous).symm) := by
    simp only [δ, Path.map_trans, ← Path.map_symm]
  let γ := δ.map zagierPullbackProjection.continuous
  let incl := continuous_inclusion zagierODERegularSet_subset_pureRegularSet
  have hγnull : (γ.map incl).Homotopic (Path.refl _) := by
    rw [show γ = δ.map zagierPullbackProjection.continuous from rfl, hprojection]
    exact (hnull r hr hrS).2 _ (τ.map zagierPullbackProjection.continuous)
      (fun t => congrArg mobiusCoordinate (hτ t)) _ (η.map zagierPullbackProjection.continuous)
  let xp : pureRegularSet := inclusion zagierODERegularSet_subset_pureRegularSet
    (zagierPullbackProjection ⟨p, zagierEndpointInterval_mem_pullback hp⟩)
  have hxp : ‖(xp : ℂ)‖ < P := hpY.trans_le (min_le_left _ _)
  obtain ⟨B, hB, hB0, hB1, hBo⟩ := hPure xp hxp (γ.map incl) hγnull
  refine ⟨p, hp, hpε, hpY.trans_le (min_le_right _ _), δ, C, ?_, ?_, ?_, ?_, B,
    hB, hB0, hB1, hBo⟩
  · simpa only [hδ0] using hC0
  · simpa only [hδ0] using hCne
  · obtain ⟨ha, ho⟩ := mem_zagierSolutionGerms_iff.mp hCo
    exact mem_zagierSolutionGerms_iff.mpr
      ⟨by simpa only [hδ0] using ha, by simpa only [hδ0] using ho⟩
  · simpa only [hδ0] using hCd

end DirichletL

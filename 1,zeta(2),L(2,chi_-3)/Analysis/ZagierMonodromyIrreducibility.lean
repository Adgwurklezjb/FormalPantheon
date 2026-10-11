import Analysis.ZagierConjugateMonodromy
import Analysis.ZagierSourceOrbit
import Analysis.ZagierSheetExchange

/-!
Full monodromy orbit spans at regular interval bases, for CDT v2, `14functions`.
The group acts on the actual fourth-order solution germs on the regular locus.
-/

namespace DirichletL

open Filter Set
open scoped Topology

attribute [local instance] Path.Homotopic.setoid

theorem zagierMonodromyOrbitSpan_eq_top {r : ℝ}
    (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) {χ : zagierSolutionGerms (mobiusCoordinate r)} (hne : χ ≠ 0) :
    zagierMonodromyOrbitSpan ⟨mobiusCoordinate r, mobiusCoordinate_regular_of_mem_Ioo hr⟩ χ = ⊤ := by
  let b : zagierODERegularSet := ⟨mobiusCoordinate r, mobiusCoordinate_regular_of_mem_Ioo hr⟩
  let P := zagierSourceSummand (zagierEndpointInterval_noncritical hr).2.1
  let Q := zagierConjugateSummand (zagierEndpointInterval_noncritical hr).2.1
  let W := zagierMonodromyOrbitSpan b χ
  have hW : W ∈ (zagierMonodromyRepresentation b).invtSubmodule :=
    zagierMonodromyOrbitSpan_mem_invtSubmodule b χ
  have hinv := (Representation.mem_invtSubmodule (zagierMonodromyRepresentation b)).mp hW
  have hχW : χ ∈ W := self_mem_zagierMonodromyOrbitSpan b χ
  obtain ⟨φ, ψ, hφ, hψ, hind⟩ := exists_zagierEndpointSolutionGerms hr
  obtain ⟨γ, δ, k, l, hk, hl, hγφ, hγψ, hδφ, hδψ, hγQ, hδQ⟩ :=
    exists_zagierEndpoint_commonBase_transport_shears_fixedConjugate hr φ ψ hφ hψ
  let g : FundamentalGroup zagierODERegularSet b :=
    FundamentalGroup.fromPath (X := TopCat.of zagierODERegularSet) ⟦γ⟧
  let h : FundamentalGroup zagierODERegularSet b :=
    FundamentalGroup.fromPath (X := TopCat.of zagierODERegularSet) ⟦δ⟧
  have hgφ : zagierMonodromyRepresentation b g φ = φ := hγφ
  have hgψ : zagierMonodromyRepresentation b g ψ = ψ + k • φ := hγψ
  have hhφ : zagierMonodromyRepresentation b h φ = φ + l • ψ := hδφ
  have hhψ : zagierMonodromyRepresentation b h ψ = ψ := hδψ
  have hgQ : ∀ u ∈ Q, zagierMonodromyRepresentation b g u ∈ Q := hγQ
  have hhQ : ∀ u ∈ Q, zagierMonodromyRepresentation b h u = u := hδQ
  obtain ⟨e, hswap⟩ := exists_zagierSheetExchange_monodromy
    (zagierEndpointInterval_noncritical hr).2.1 (mobiusCoordinate_regular_of_mem_Ioo hr)
  have hPQ : IsCompl P Q := isCompl_zagierSolutionSummands
    (zagierEndpointInterval_noncritical hr).2.1 (mobiusCoordinate_regular_of_mem_Ioo hr)
  have hψP : ψ ∈ P := ⟨zagierEndpointSolution,
    (zagierEndpointInterval_solutions hr).2.2.1,
    (zagierEndpointInterval_solutions hr).2.2.2, hψ⟩
  have hψne : ψ ≠ 0 := by
    simpa only [Matrix.cons_val_one, Matrix.cons_val_fin_one] using
      LinearIndependent.ne_zero (1 : Fin 2) hind
  have hextract : ∃ u : zagierSolutionGerms (mobiusCoordinate r), u ∈ P ∧ u ∈ W ∧ u ≠ 0 := by
    by_cases hχQ : χ ∈ Q
    · refine ⟨zagierMonodromyRepresentation b e χ, (hswap χ).2.mpr hχQ, hinv e hχW, ?_⟩
      intro he
      apply hne
      apply (zagierMonodromy b e).injective
      simpa only [map_zero] using he
    · have hsup : χ ∈ P ⊔ Q := by rw [hPQ.sup_eq_top]; trivial
      obtain ⟨v, hv, c, hc, hsum⟩ := Submodule.mem_sup.mp hsup
      have hspan : P = Submodule.span ℂ {φ, ψ} :=
        zagierSourceSummand_eq_span_endpoint hr φ ψ hφ hψ
      obtain ⟨a, d, had⟩ := Submodule.mem_span_pair.mp (hspan ▸ hv)
      have hχ : χ = a • φ + d • ψ + c :=
        hsum.symm.trans (congrArg (fun u => u + c) had.symm)
      have hψW : ψ ∈ W := by
        by_cases ha : a = 0
        · have hd : d ≠ 0 := by
            intro hd
            apply hχQ
            simpa only [hχ, ha, hd, zero_smul, zero_add] using hc
          have hgc : zagierMonodromyRepresentation b g χ =
              (d * k) • φ + d • ψ + zagierMonodromyRepresentation b g c := by
            rw [hχ, map_add, map_add, map_smul, map_smul, hgφ, hgψ]
            simp only [ha, zero_smul, zero_add, smul_add, mul_smul]
            abel
          have he : zagierMonodromyRepresentation b h (zagierMonodromyRepresentation b g χ) -
              zagierMonodromyRepresentation b g χ = (d * k * l) • ψ := by
            rw [hgc, map_add, map_add, map_smul, map_smul, hhφ, hhψ, hhQ _ (hgQ c hc)]
            simp only [smul_add, mul_smul]
            abel
          apply (W.smul_mem_iff (mul_ne_zero (mul_ne_zero hd hk) hl)).mp
          rw [← he]
          exact W.sub_mem (hinv h (hinv g hχW)) (hinv g hχW)
        · have he : zagierMonodromyRepresentation b h χ - χ = (a * l) • ψ := by
            rw [hχ, map_add, map_add, map_smul, map_smul, hhφ, hhψ, hhQ c hc]
            simp only [smul_add, mul_smul]
            abel
          apply (W.smul_mem_iff (mul_ne_zero ha hl)).mp
          rw [← he]
          exact W.sub_mem (hinv h hχW) hχW
      exact ⟨ψ, hψP, hψW, hψne⟩
  obtain ⟨u, huP, huW, hune⟩ := hextract
  have hPW : P ≤ W := (zagierSourceSummand_le_orbitSpan_of_mem hr huP hune).trans
    (zagierMonodromyOrbitSpan_le b hW huW)
  have hQW : Q ≤ W := by
    intro u hu
    let v := (zagierMonodromy b e).symm u
    have he : zagierMonodromyRepresentation b e v = u := (zagierMonodromy b e).apply_symm_apply u
    have hvP : v ∈ P := (hswap v).1.mp (by
      change zagierMonodromyRepresentation b e v ∈ Q
      rwa [he])
    have hvW : zagierMonodromyRepresentation b e v ∈ W := hinv e (hPW hvP)
    rwa [he] at hvW
  change W = ⊤
  apply eq_top_iff.mpr
  rw [← hPQ.sup_eq_top]
  exact sup_le hPW hQW

end DirichletL

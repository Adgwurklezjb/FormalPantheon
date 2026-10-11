import Analysis.PureFunctionContinuation
import Analysis.ZagierConjugateLoops

/-!
Invariance of the literal pure-seven family on CDT's endpoint loops and
their conjugates, for v2 Lemma `14functions` (TeX lines 8074-8097).
The exact projected paths stay fourth-order regular. Their contractions
take place in the larger pure domain, C minus {0,4}.
-/

namespace DirichletL

open Filter Set unitInterval
open scoped Topology Matrix

theorem zagierODERegularSet_subset_pureRegularSet : zagierODERegularSet ⊆ pureRegularSet := by
  intro z hz
  obtain ⟨hz0, hz4, _⟩ := (mem_zagierODERegularSet_iff z).mp hz
  exact (mem_pureRegularSet_iff z).mpr ⟨hz0, hz4⟩

theorem pureRegular_homotopic_refl_of_range_subset_ball {x : pureRegularSet} (γ : Path x x)
    {c : ℂ} {R : ℝ} (hball : Metric.ball c R ⊆ pureRegularSet)
    (hγ : ∀ t, (γ t : ℂ) ∈ Metric.ball c R) : γ.Homotopic (Path.refl x) := by
  have hx : (x : ℂ) ∈ Metric.ball c R := by simpa only [Path.source] using hγ 0
  letI := (convex_ball c R).contractibleSpace ⟨(x : ℂ), hx⟩
  let η : Path (⟨(x : ℂ), hx⟩ : Metric.ball c R) ⟨(x : ℂ), hx⟩ :=
    { toFun := fun t => ⟨(γ t : ℂ), hγ t⟩
      continuous_toFun := (continuous_subtype_val.comp γ.continuous).subtype_mk _
      source' := Subtype.ext (congrArg (fun z : pureRegularSet => (z : ℂ)) γ.source)
      target' := Subtype.ext (congrArg (fun z : pureRegularSet => (z : ℂ)) γ.target) }
  have hη := (SimplyConnectedSpace.paths_homotopic η (Path.refl _)).map
    (ContinuousMap.inclusion hball)
  have he : η.map (continuous_inclusion hball) = γ := by
    apply Path.ext
    rfl
  have hr : (Path.refl (⟨(x : ℂ), hx⟩ : Metric.ball c R)).map
      (continuous_inclusion hball) = Path.refl x := by
    apply Path.ext
    rfl
  rwa [he, hr] at hη

theorem exists_zagierEndpointCircle_pure_conjugate_homotopic_refl :
    ∃ S : ℝ, 0 < S ∧ ∀ r : ℝ, ∀ hr : r ∈ Ioo 0 (1 / 9 : ℝ), r < S →
      (∀ t : I, mobiusCoordinate (zagierEndpointCirclePath r hr t) ∈ zagierODERegularSet) ∧
      ∀ (b : zagierODERegularSet) (γ : Path b b),
        (∀ t, (γ t : ℂ) = mobiusCoordinate (zagierEndpointCirclePath r hr t)) →
        ∀ (x : zagierODERegularSet) (η : Path x b),
          (((η.trans γ).trans η.symm).map
            (continuous_inclusion zagierODERegularSet_subset_pureRegularSet)).Homotopic
            (Path.refl (Set.inclusion zagierODERegularSet_subset_pureRegularSet x)) := by
  have hc : (-1 / 72 : ℂ) ∈ pureRegularSet := by norm_num [mem_pureRegularSet_iff]
  obtain ⟨E, hE, hEball⟩ := Metric.mem_nhds_iff.mp (isOpen_pureRegularSet.mem_nhds hc)
  have hT : Tendsto mobiusCoordinate (𝓝 (1 / 9 : ℂ)) (𝓝 (-1 / 72 : ℂ)) := by
    simpa only [mobiusCoordinate_one_div_nine] using
      (analyticAt_mobiusCoordinate (by norm_num : (1 / 9 : ℂ) ≠ 1)).continuousAt.tendsto
  obtain ⟨R, hR, hRball⟩ := Metric.mem_nhds_iff.mp
    (hT.eventually (Metric.ball_mem_nhds (-1 / 72 : ℂ) hE))
  obtain ⟨S, hS, hcircle⟩ := exists_zagierEndpointCircle_radius_subset_ball hR
  obtain ⟨T, hT, hreg⟩ := exists_zagierPullback_circle_radius
  refine ⟨min S T, lt_min hS hT, ?_⟩
  intro r hr hrST
  refine ⟨fun t => (hreg r hr (hrST.trans_le (min_le_right _ _)) t).2, ?_⟩
  intro b γ hγ x η
  let incl := continuous_inclusion zagierODERegularSet_subset_pureRegularSet
  have hγnull : (γ.map incl).Homotopic
      (Path.refl (Set.inclusion zagierODERegularSet_subset_pureRegularSet b)) := by
    apply pureRegular_homotopic_refl_of_range_subset_ball _ hEball
    intro t
    change (γ t : ℂ) ∈ Metric.ball (-1 / 72 : ℂ) E
    rw [hγ t]
    exact hRball (hcircle r hr (hrST.trans_le (min_le_left _ _)) t)
  have h₁ := ((Path.Homotopic.refl (η.map incl)).hcomp hγnull).hcomp
    (Path.Homotopic.refl (η.map incl).symm)
  have h₂ : ((η.map incl).trans (Path.refl _)).Homotopic (η.map incl) :=
    ⟨Path.Homotopy.transRefl (η.map incl)⟩
  have h₃ : ((η.map incl).trans (η.map incl).symm).Homotopic (Path.refl _) :=
    ⟨(Path.Homotopy.reflTransSymm (η.map incl)).symm⟩
  simpa only [Path.map_trans, ← Path.map_symm] using
    (h₁.trans (h₂.hcomp (Path.Homotopic.refl (η.map incl).symm))).trans h₃

theorem exists_pureSeven_zagierEndpointCircle_conjugate_continuation :
    ∃ R : ℝ, 0 < R ∧ ∃ S : ℝ, 0 < S ∧
      ∀ r : ℝ, ∀ hr : r ∈ Ioo 0 (1 / 9 : ℝ), r < S →
        ∃ (b : zagierODERegularSet) (γ : Path b b),
          (∀ t, (γ t : ℂ) = mobiusCoordinate (zagierEndpointCirclePath r hr t)) ∧
          ∀ x : zagierODERegularSet, ‖(x : ℂ)‖ < R → ∀ η : Path x b,
            ∃ F : I → ℂ → Fin 7 → ℂ,
              (∀ i, AnalyticContinuationAlong (fun t => (((η.trans γ).trans η.symm) t : ℂ))
                (fun t z => F t z i)) ∧
              F 0 =ᶠ[𝓝 (x : ℂ)] pureSevenState ∧ F 1 =ᶠ[𝓝 (x : ℂ)] pureSevenState ∧
              ∀ t, ∀ᶠ z in 𝓝 (((η.trans γ).trans η.symm) t : ℂ),
                HasDerivAt (F t) (pureSevenMatrix z *ᵥ F t z) z := by
  obtain ⟨R, hR, hcont⟩ := exists_analyticContinuationAlong_pureSeven_homotopic_refl
  obtain ⟨S, hS, hcircle⟩ := exists_zagierEndpointCircle_pure_conjugate_homotopic_refl
  refine ⟨R, hR, S, hS, ?_⟩
  intro r hr hrS
  obtain ⟨hreg, hnull⟩ := hcircle r hr hrS
  have hne (t : I) : zagierEndpointCirclePath r hr t ≠ 1 :=
    zagierEndpointCoordinate_ne_one
      (complexCirclePath_ne_one (by rw [abs_of_pos hr.1]; linarith [hr.2]) t)
  let γ := zagierMobiusPath (zagierEndpointCirclePath r hr) hne hreg
  refine ⟨_, γ, fun _ => rfl, ?_⟩
  intro x hx η
  exact hcont (Set.inclusion zagierODERegularSet_subset_pureRegularSet x) hx
    (((η.trans γ).trans η.symm).map
      (continuous_inclusion zagierODERegularSet_subset_pureRegularSet))
    (hnull _ γ (fun _ => rfl) x η)

theorem pureSeven_zagierEndpointCircle_conjugate_end_eq :
    ∃ R : ℝ, 0 < R ∧ ∃ S : ℝ, 0 < S ∧
      ∀ r : ℝ, ∀ hr : r ∈ Ioo 0 (1 / 9 : ℝ), r < S →
        ∀ (b : zagierODERegularSet) (γ : Path b b),
          (∀ t, (γ t : ℂ) = mobiusCoordinate (zagierEndpointCirclePath r hr t)) →
          ∀ x : zagierODERegularSet, ‖(x : ℂ)‖ < R → ∀ η : Path x b,
            ∀ F : I → ℂ → Fin 7 → ℂ,
              (∀ i, AnalyticContinuationAlong (fun t => (((η.trans γ).trans η.symm) t : ℂ))
                (fun t z => F t z i)) →
              F 0 =ᶠ[𝓝 (x : ℂ)] pureSevenState → F 1 =ᶠ[𝓝 (x : ℂ)] pureSevenState := by
  obtain ⟨R, hR, hend⟩ := pureSeven_continuation_end_eq_of_homotopic_refl
  obtain ⟨S, hS, hcircle⟩ := exists_zagierEndpointCircle_pure_conjugate_homotopic_refl
  refine ⟨R, hR, S, hS, ?_⟩
  intro r hr hrS b γ hγ x hx η F hF hF0
  exact hend (Set.inclusion zagierODERegularSet_subset_pureRegularSet x) hx
    (((η.trans γ).trans η.symm).map
      (continuous_inclusion zagierODERegularSet_subset_pureRegularSet))
    ((hcircle r hr hrS).2 b γ hγ x η) F hF hF0

end DirichletL

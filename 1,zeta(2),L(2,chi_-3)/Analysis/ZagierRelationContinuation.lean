import Analysis.ZagierMonodromy
import Analysis.ZagierPolynomialRelations

/-!
Continuation of polynomial differential relations in CDT v2, Lemma `14functions`.
The relation kernels are invariant under the actual monodromy representation.
The later `ZagierDerivativeIndependence` module supplies irreducibility at interval bases.
-/

namespace DirichletL

open Filter unitInterval
open scoped Topology

theorem isLocallyConstant_zagierPolynomialRelation (b : zagierODERegularSet)
    (P : Fin 4 → Polynomial ℂ) {T : Type*} [TopologicalSpace T]
    {u : T → ZagierContinuation b} (hu : Continuous u) :
    IsLocallyConstant (fun t =>
      (u t).snd ∈ zagierPolynomialRelationSubmodule P ((u t).proj : ℂ)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro t
  obtain ⟨e, ht, f, hf, _, hrep⟩ :=
    exists_zagierContinuation_local_representative b (hu.continuousAt (x := t))
  have hrt := hrep.self_of_nhds
  filter_upwards [hrep] with s hs
  apply propext
  rw [mem_zagierPolynomialRelationSubmodule_iff P (u s).snd hs.2,
    mem_zagierPolynomialRelationSubmodule_iff P (u t).snd hrt.2]
  constructor
  · intro h
    have he := zagierPolynomialResidual_eqOn_of_preconnected P hf
      (convex_ball e.center e.radius).isPreconnected hs.1 h
    exact Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds ht) (fun z hz => he hz)
  · intro h
    have he := zagierPolynomialResidual_eqOn_of_preconnected P hf
      (convex_ball e.center e.radius).isPreconnected ht h
    exact Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hs.1) (fun z hz => he hz)

/-- A regular path preserves a polynomial differential relation in both directions. -/
theorem zagierPathTransport_mem_polynomialRelation_iff (b : zagierODERegularSet)
    (P : Fin 4 → Polynomial ℂ) {x y : zagierODERegularSet} (γ : Path x y)
    (φ : zagierSolutionGerms (x : ℂ)) :
    zagierPathTransport b γ φ ∈ zagierPolynomialRelationSubmodule P (y : ℂ) ↔
      φ ∈ zagierPolynomialRelationSubmodule P (x : ℂ) := by
  have hc := isLocallyConstant_zagierPolynomialRelation b P
    (u := fun t => zagierPathLift b γ φ t) (zagierPathLift b γ φ).continuous
  have h := hc.apply_eq_of_preconnectedSpace (1 : I) 0
  let R : ZagierContinuation b → Prop :=
    fun p => p.snd ∈ zagierPolynomialRelationSubmodule P (p.proj : ℂ)
  have h1 := congrArg R (zagierPathLift_one b γ φ)
  have h0 := congrArg R (zagierPathLift_zero b γ φ)
  exact Iff.of_eq (h1.symm.trans (h.trans h0))

theorem zagierMonodromy_mem_polynomialRelation_iff (b : zagierODERegularSet)
    (P : Fin 4 → Polynomial ℂ) (g : FundamentalGroup zagierODERegularSet b)
    (φ : zagierSolutionGerms (b : ℂ)) :
    zagierMonodromyRepresentation b g φ ∈ zagierPolynomialRelationSubmodule P (b : ℂ) ↔
      φ ∈ zagierPolynomialRelationSubmodule P (b : ℂ) := by
  change zagierHomotopyTransport b g.hom φ ∈ zagierPolynomialRelationSubmodule P (b : ℂ) ↔ _
  generalize g.hom = Q
  induction Q using Quotient.inductionOn with
  | _ γ => exact zagierPathTransport_mem_polynomialRelation_iff b P γ φ

/-- Polynomial differential-relation kernels are invariant under actual monodromy. -/
theorem zagierPolynomialRelationSubmodule_mem_invtSubmodule (b : zagierODERegularSet)
    (P : Fin 4 → Polynomial ℂ) :
    zagierPolynomialRelationSubmodule P (b : ℂ) ∈
      (zagierMonodromyRepresentation b).invtSubmodule := by
  rw [Representation.mem_invtSubmodule]
  intro g
  rw [Module.End.mem_invtSubmodule]
  intro φ hφ
  exact (zagierMonodromy_mem_polynomialRelation_iff b P g φ).mpr hφ

theorem zagierMonodromyOrbitSpan_le_polynomialRelationSubmodule (b : zagierODERegularSet)
    (P : Fin 4 → Polynomial ℂ) {φ : zagierSolutionGerms (b : ℂ)}
    (hφ : φ ∈ zagierPolynomialRelationSubmodule P (b : ℂ)) :
    zagierMonodromyOrbitSpan b φ ≤ zagierPolynomialRelationSubmodule P (b : ℂ) :=
  zagierMonodromyOrbitSpan_le b (zagierPolynomialRelationSubmodule_mem_invtSubmodule b P) hφ

theorem eq_zero_of_zagierPolynomialRelation_of_orbitSpan_eq_top (b : zagierODERegularSet)
    (P : Fin 4 → Polynomial ℂ) {φ : zagierSolutionGerms (b : ℂ)}
    (hφ : φ ∈ zagierPolynomialRelationSubmodule P (b : ℂ))
    (hspan : zagierMonodromyOrbitSpan b φ = ⊤) : P = 0 := by
  apply (zagierPolynomialRelationSubmodule_eq_top_iff b P).mp
  apply top_unique
  rw [← hspan]
  exact zagierMonodromyOrbitSpan_le_polynomialRelationSubmodule b P hφ

/-- Irreducibility excludes polynomial relations on a nonzero solution germ. -/
theorem eq_zero_of_zagierPolynomialRelation_of_isSimpleOrder (b : zagierODERegularSet)
    (P : Fin 4 → Polynomial ℂ)
    (hI : IsSimpleOrder (zagierMonodromyRepresentation b).invtSubmodule)
    {φ : zagierSolutionGerms (b : ℂ)} (hφ : φ ≠ 0)
    (hrel : φ ∈ zagierPolynomialRelationSubmodule P (b : ℂ)) : P = 0 := by
  letI := hI
  let W : (zagierMonodromyRepresentation b).invtSubmodule :=
    ⟨zagierPolynomialRelationSubmodule P (b : ℂ),
      zagierPolynomialRelationSubmodule_mem_invtSubmodule b P⟩
  have hW : W ≠ ⊥ := by
    intro h
    have hk : zagierPolynomialRelationSubmodule P (b : ℂ) = ⊥ := congrArg Subtype.val h
    rw [hk, Submodule.mem_bot] at hrel
    exact hφ hrel
  have ht : W = ⊤ := (eq_bot_or_eq_top W).resolve_left hW
  exact (zagierPolynomialRelationSubmodule_eq_top_iff b P).mp (congrArg Subtype.val ht)

/-- The actual analytic G_A germ at a regular point in its verified convergence disk. -/
noncomputable def zagierPrincipalSolutionGerm (b : zagierODERegularSet)
    (hb : ‖(b : ℂ)‖ < 1 / 648) : zagierSolutionGerms (b : ℂ) :=
  zagierSolutionGermOfFun (symmetrizedAnalytic hA) (analyticAt_symmetrizedAnalytic_hA hb) (by
    have hb' : (b : ℂ) ∈ Metric.ball 0 (1 / 648) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hb
    filter_upwards [Metric.isOpen_ball.mem_nhds hb'] with z hz
    exact zagierAnalyticODE_symmetrizedAnalytic_hA
      (by simpa only [Metric.mem_ball, dist_zero_right] using hz))

@[simp]
theorem zagierPrincipalSolutionGerm_coe (b : zagierODERegularSet)
    (hb : ‖(b : ℂ)‖ < 1 / 648) :
    (zagierPrincipalSolutionGerm b hb : Germ (𝓝 (b : ℂ)) ℂ) = symmetrizedAnalytic hA := rfl

theorem zagierPrincipalSolutionGerm_ne_zero (b : zagierODERegularSet)
    (hb : ‖(b : ℂ)‖ < 1 / 648) : zagierPrincipalSolutionGerm b hb ≠ 0 := by
  intro h
  have hs := congrArg (zagierSolutionGermState (b : ℂ)) h
  apply zagierODEState_symmetrizedAnalytic_hA_ne_zero hb b.property
  simpa only [zagierPrincipalSolutionGerm, zagierSolutionGermState_ofFun, map_zero] using hs

/-- The principal solution criterion retains the irreducibility hypothesis explicitly. -/
theorem eq_zero_of_zagierPolynomialResidual_hA_of_isSimpleOrder (b : zagierODERegularSet)
    (hb : ‖(b : ℂ)‖ < 1 / 648)
    (hI : IsSimpleOrder (zagierMonodromyRepresentation b).invtSubmodule)
    (P : Fin 4 → Polynomial ℂ)
    (hrel : zagierPolynomialResidual P (symmetrizedAnalytic hA) =ᶠ[𝓝 (b : ℂ)] 0) : P = 0 := by
  apply eq_zero_of_zagierPolynomialRelation_of_isSimpleOrder b P hI
    (zagierPrincipalSolutionGerm_ne_zero b hb)
  exact (mem_zagierPolynomialRelationSubmodule_iff P _
    (zagierPrincipalSolutionGerm_coe b hb)).mpr hrel

end DirichletL

import Analysis.ZagierSolutionGerms

/-!
Local solution frames and germ coordinates for CDT v2 equation `explicitode`.
They prepare the continuation atlas used by the monodromy argument in Lemma `14functions`.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

/-- A normalized solution frame on a regular ball. -/
structure ZagierSolutionFrame where
  /-- Center of the regular solution ball. -/
  center : ℂ
  /-- Radius of the regular solution ball. -/
  radius : ℝ
  radius_pos : 0 < radius
  regular : Metric.ball center radius ⊆ zagierODERegularSet
  /-- Four scalar solutions with the standard initial derivative states. -/
  solution : Fin 4 → ℂ → ℂ
  analytic : ∀ j, AnalyticOnNhd ℂ (solution j) (Metric.ball center radius)
  equation : ∀ j, Set.EqOn (zagierAnalyticODE (solution j)) 0 (Metric.ball center radius)
  initial : ∀ j, zagierODEState (solution j) center = Pi.single j 1

namespace ZagierSolutionFrame

theorem exists_center {x : ℂ} (hx : x ∈ zagierODERegularSet) :
    ∃ e : ZagierSolutionFrame, e.center = x := by
  obtain ⟨r, f, hr, hreg, hf, hode, hinit, _⟩ := exists_zagierODE_fundamental_solutions hx
  exact ⟨⟨x, r, hr, hreg, f, hf, hode, hinit⟩, rfl⟩

/-- Choose a normalized frame centered at a given regular point. -/
noncomputable def atPoint (x : zagierODERegularSet) : ZagierSolutionFrame :=
  (exists_center x.property).choose

@[simp]
theorem atPoint_center (x : zagierODERegularSet) : (atPoint x).center = x :=
  (exists_center x.property).choose_spec

/-- The frame ball as a subset of the regular base space. -/
def baseSet (e : ZagierSolutionFrame) : Set zagierODERegularSet :=
  {x | (x : ℂ) ∈ Metric.ball e.center e.radius}

theorem isOpen_baseSet (e : ZagierSolutionFrame) : IsOpen e.baseSet :=
  Metric.isOpen_ball.preimage continuous_subtype_val

theorem mem_baseSet_atPoint (x : zagierODERegularSet) : x ∈ (atPoint x).baseSet := by
  change dist (x : ℂ) (atPoint x).center < (atPoint x).radius
  rw [atPoint_center, dist_self]
  exact (atPoint x).radius_pos

theorem isUnit_matrix (e : ZagierSolutionFrame) {x : ℂ}
    (hx : x ∈ Metric.ball e.center e.radius) :
    IsUnit (zagierFundamentalMatrix e.solution x) := by
  apply isUnit_zagierFundamentalMatrix_of_initial Metric.isOpen_ball
    (convex_ball e.center e.radius).isPreconnected (Metric.mem_ball_self e.radius_pos)
    hx e.regular e.analytic e.equation
  rw [zagierFundamentalMatrix_eq_one e.initial]
  exact isUnit_one

/-- Frame coefficients, labeled by the states in a fixed model germ fiber. -/
noncomputable def coordinates (e : ZagierSolutionFrame) (b x : zagierODERegularSet) :
    zagierSolutionGerms (x : ℂ) →ₗ[ℂ] zagierSolutionGerms (b : ℂ) :=
  (zagierSolutionGermStateEquiv b.property).symm.toLinearMap.comp
    (((zagierFundamentalMatrix e.solution x)⁻¹).mulVecLin.comp (zagierSolutionGermState x))

/-- Realize constant frame coefficients as a solution germ at a regular point. -/
noncomputable def fromCoordinates (e : ZagierSolutionFrame) (b x : zagierODERegularSet) :
    zagierSolutionGerms (b : ℂ) →ₗ[ℂ] zagierSolutionGerms (x : ℂ) :=
  (zagierSolutionGermStateEquiv x.property).symm.toLinearMap.comp
    ((zagierFundamentalMatrix e.solution x).mulVecLin.comp (zagierSolutionGermState b))

theorem state_coordinates (e : ZagierSolutionFrame) (b x : zagierODERegularSet)
    (φ : zagierSolutionGerms (x : ℂ)) :
    zagierSolutionGermState b (e.coordinates b x φ) =
      (zagierFundamentalMatrix e.solution x)⁻¹ *ᵥ zagierSolutionGermState x φ := by
  simp [coordinates, Matrix.mulVecLin_apply]

theorem state_fromCoordinates (e : ZagierSolutionFrame) (b x : zagierODERegularSet)
    (c : zagierSolutionGerms (b : ℂ)) :
    zagierSolutionGermState x (e.fromCoordinates b x c) =
      zagierFundamentalMatrix e.solution x *ᵥ zagierSolutionGermState b c := by
  simp [fromCoordinates, Matrix.mulVecLin_apply]

theorem fromCoordinates_coordinates (e : ZagierSolutionFrame) (b x : zagierODERegularSet)
    (hx : x ∈ e.baseSet) (φ : zagierSolutionGerms (x : ℂ)) :
    e.fromCoordinates b x (e.coordinates b x φ) = φ := by
  apply zagierSolutionGermState_injective x.property
  rw [state_fromCoordinates, state_coordinates, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (e.isUnit_matrix hx)),
    Matrix.one_mulVec]

theorem coordinates_fromCoordinates (e : ZagierSolutionFrame) (b x : zagierODERegularSet)
    (hx : x ∈ e.baseSet) (c : zagierSolutionGerms (b : ℂ)) :
    e.coordinates b x (e.fromCoordinates b x c) = c := by
  apply zagierSolutionGermState_injective b.property
  rw [state_coordinates, state_fromCoordinates, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (e.isUnit_matrix hx)),
    Matrix.one_mulVec]

/-- The coordinate equivalence is valid over the entire frame ball. -/
noncomputable def coordinatesEquiv (e : ZagierSolutionFrame) (b x : zagierODERegularSet)
    (hx : x ∈ e.baseSet) : zagierSolutionGerms (x : ℂ) ≃ₗ[ℂ] zagierSolutionGerms (b : ℂ) :=
  { e.coordinates b x with
    invFun := e.fromCoordinates b x
    left_inv := e.fromCoordinates_coordinates b x hx
    right_inv := e.coordinates_fromCoordinates b x hx }

/-- The analytic scalar function with constant frame coefficients. -/
noncomputable def scalarSection (e : ZagierSolutionFrame) (b : zagierODERegularSet)
    (c : zagierSolutionGerms (b : ℂ)) : ℂ → ℂ :=
  fun z => ∑ j, zagierSolutionGermState b c j • e.solution j z

theorem analyticOnNhd_scalarSection (e : ZagierSolutionFrame) (b : zagierODERegularSet)
    (c : zagierSolutionGerms (b : ℂ)) :
    AnalyticOnNhd ℂ (e.scalarSection b c) (Metric.ball e.center e.radius) :=
  Finset.univ.analyticOnNhd_sum (fun j _ z hz =>
    (e.analytic j z hz).const_smul (c := zagierSolutionGermState b c j))

theorem ode_scalarSection (e : ZagierSolutionFrame) (b : zagierODERegularSet)
    (c : zagierSolutionGerms (b : ℂ)) :
    Set.EqOn (zagierAnalyticODE (e.scalarSection b c)) 0 (Metric.ball e.center e.radius) := by
  intro z hz
  unfold scalarSection
  rw [zagierAnalyticODE_sum (fun j => e.analytic j z hz)]
  simp only [e.equation _ hz, smul_zero, Finset.sum_const_zero, Pi.zero_apply]

theorem state_scalarSection (e : ZagierSolutionFrame) (b : zagierODERegularSet)
    (c : zagierSolutionGerms (b : ℂ)) {x : ℂ} (hx : x ∈ Metric.ball e.center e.radius) :
    zagierODEState (e.scalarSection b c) x =
      zagierFundamentalMatrix e.solution x *ᵥ zagierSolutionGermState b c := by
  unfold scalarSection
  rw [zagierODEState_sum (fun j => e.analytic j x hx), zagierFundamentalMatrix_mulVec]

theorem fromCoordinates_eq_scalarSection_germ (e : ZagierSolutionFrame)
    (b x : zagierODERegularSet) (hx : x ∈ e.baseSet) (c : zagierSolutionGerms (b : ℂ)) :
    (e.fromCoordinates b x c : Germ (𝓝 (x : ℂ)) ℂ) = e.scalarSection b c := by
  have hode : zagierAnalyticODE (e.scalarSection b c) =ᶠ[𝓝 (x : ℂ)] 0 :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hx)
      (fun z hz => e.ode_scalarSection b c hz)
  have he : e.fromCoordinates b x c =
      zagierSolutionGermOfFun (e.scalarSection b c)
        (e.analyticOnNhd_scalarSection b c x hx) hode := by
    apply zagierSolutionGermState_injective x.property
    rw [state_fromCoordinates, zagierSolutionGermState_ofFun, state_scalarSection e b c hx]
  exact congrArg Subtype.val he

end ZagierSolutionFrame

end DirichletL

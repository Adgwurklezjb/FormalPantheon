import Analysis.AnalyticLinearODEGerms

/-!
Normalized local frames for finite analytic matrix systems. These give the
constant local coordinates needed for continuation in CDT v2, `14functions`.
-/

namespace DirichletL.AnalyticMatrixODE

open Filter
open scoped Topology Matrix

variable {I : Type*} [Fintype I] (D : AnalyticMatrixODE I)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
attribute [local instance] Classical.propDecidable

/-- A normalized vector solution frame on a ball contained in the analytic domain. -/
structure SolutionFrame where
  /-- Center at which the frame has the standard initial vectors. -/
  center : ℂ
  /-- Radius of the common analytic solution ball. -/
  radius : ℝ
  radius_pos : 0 < radius
  regular : Metric.ball center radius ⊆ D.domain
  /-- One vector solution for each standard initial vector. -/
  solution : I → ℂ → I → ℂ
  analytic : ∀ j, AnalyticOnNhd ℂ (solution j) (Metric.ball center radius)
  equation : ∀ j z, z ∈ Metric.ball center radius →
    HasDerivAt (solution j) (D.matrix z *ᵥ solution j z) z
  initial : ∀ j, solution j center = Pi.single j 1

namespace SolutionFrame

variable {D}

theorem exists_center {x : ℂ} (hx : x ∈ D.domain) :
    ∃ e : D.SolutionFrame, e.center = x := by
  classical
  choose f hf hinit hode using
    (fun j : I => exists_analytic_matrix_ode (D.analytic x hx) (Pi.single j 1))
  have hall : ∀ᶠ z in 𝓝 x, z ∈ D.domain ∧
      ∀ j, AnalyticAt ℂ (f j) z ∧ HasDerivAt (f j) (D.matrix z *ᵥ f j z) z := by
    filter_upwards [D.isOpen_domain.mem_nhds hx,
      Filter.eventually_all.mpr (fun j => (hf j).eventually_analyticAt.and (hode j))]
      with z hz hzs
    exact ⟨hz, hzs⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hall
  exact ⟨⟨x, r, hr, fun z hz => (hball z hz).1,
    f, fun j z hz => ((hball z hz).2 j).1,
    fun j z hz => ((hball z hz).2 j).2, hinit⟩, rfl⟩

/-- Choose a normalized frame centered at a domain point. -/
noncomputable def atPoint (x : D.domain) : D.SolutionFrame :=
  (exists_center x.property).choose

@[simp]
theorem atPoint_center (x : D.domain) : (atPoint x).center = x :=
  (exists_center x.property).choose_spec

/-- The frame ball viewed inside the domain subtype. -/
def baseSet (e : D.SolutionFrame) : Set D.domain :=
  {x | (x : ℂ) ∈ Metric.ball e.center e.radius}

theorem isOpen_baseSet (e : D.SolutionFrame) : IsOpen e.baseSet :=
  Metric.isOpen_ball.preimage continuous_subtype_val

theorem mem_baseSet_atPoint (x : D.domain) : x ∈ (atPoint x).baseSet := by
  change dist (x : ℂ) (atPoint x).center < (atPoint x).radius
  rw [atPoint_center, dist_self]
  exact (atPoint x).radius_pos

/-- Columns are vector solution values. -/
def matrix (e : D.SolutionFrame) (z : ℂ) : Matrix I I ℂ := fun i j => e.solution j z i

theorem matrix_mulVec (e : D.SolutionFrame) (z : ℂ) (c : I → ℂ) :
    e.matrix z *ᵥ c = ∑ j, c j • e.solution j z := by
  ext i
  simp [matrix, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem isUnit_matrix (e : D.SolutionFrame) {x : ℂ}
    (hx : x ∈ Metric.ball e.center e.radius) : IsUnit (e.matrix x) := by
  classical
  have hcenter : e.center ∈ Metric.ball e.center e.radius := Metric.mem_ball_self e.radius_pos
  have hi : LinearIndependent ℂ (fun j => fun z : Metric.ball e.center e.radius =>
      e.solution j z) :=
    (linearIndependent_iff_initialValue_of_analytic_matrix_ode Metric.isOpen_ball
      (convex_ball e.center e.radius).isPreconnected hcenter
      (D.analytic e.center (e.regular hcenter)).continuousAt e.analytic e.equation).mpr
      (by simpa only [e.initial] using Pi.linearIndependent_single_one I ℂ)
  apply Matrix.linearIndependent_cols_iff_isUnit.mp
  exact (linearIndependent_iff_initialValue_of_analytic_matrix_ode Metric.isOpen_ball
    (convex_ball e.center e.radius).isPreconnected hx
    (D.analytic x (e.regular hx)).continuousAt e.analytic e.equation).mp hi

/-- Frame coefficients labeled by a fixed model fiber. -/
noncomputable def coordinates (e : D.SolutionFrame) (b x : D.domain) :
    D.solutionGerms (x : ℂ) →ₗ[ℂ] D.solutionGerms (b : ℂ) :=
  (D.germValueEquiv b.property).symm.toLinearMap.comp
    (((e.matrix x)⁻¹).mulVecLin.comp (D.germValue x))

/-- Realize constant frame coefficients as a germ at a domain point. -/
noncomputable def fromCoordinates (e : D.SolutionFrame) (b x : D.domain) :
    D.solutionGerms (b : ℂ) →ₗ[ℂ] D.solutionGerms (x : ℂ) :=
  (D.germValueEquiv x.property).symm.toLinearMap.comp
    ((e.matrix x).mulVecLin.comp (D.germValue b))

theorem value_coordinates (e : D.SolutionFrame) (b x : D.domain)
    (φ : D.solutionGerms (x : ℂ)) :
    D.germValue b (e.coordinates b x φ) = (e.matrix x)⁻¹ *ᵥ D.germValue x φ := by
  simp [coordinates, Matrix.mulVecLin_apply]

theorem value_fromCoordinates (e : D.SolutionFrame) (b x : D.domain)
    (c : D.solutionGerms (b : ℂ)) :
    D.germValue x (e.fromCoordinates b x c) = e.matrix x *ᵥ D.germValue b c := by
  simp [fromCoordinates, Matrix.mulVecLin_apply]

theorem fromCoordinates_coordinates (e : D.SolutionFrame) (b x : D.domain)
    (hx : x ∈ e.baseSet) (φ : D.solutionGerms (x : ℂ)) :
    e.fromCoordinates b x (e.coordinates b x φ) = φ := by
  apply D.germValue_injective x.property
  rw [value_fromCoordinates, value_coordinates, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (e.isUnit_matrix hx)),
    Matrix.one_mulVec]

theorem coordinates_fromCoordinates (e : D.SolutionFrame) (b x : D.domain)
    (hx : x ∈ e.baseSet) (c : D.solutionGerms (b : ℂ)) :
    e.coordinates b x (e.fromCoordinates b x c) = c := by
  apply D.germValue_injective b.property
  rw [value_coordinates, value_fromCoordinates, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (e.isUnit_matrix hx)),
    Matrix.one_mulVec]

/-- Germ coordinates are a linear equivalence throughout the frame ball. -/
noncomputable def coordinatesEquiv (e : D.SolutionFrame) (b x : D.domain)
    (hx : x ∈ e.baseSet) : D.solutionGerms (x : ℂ) ≃ₗ[ℂ] D.solutionGerms (b : ℂ) :=
  { e.coordinates b x with
    invFun := e.fromCoordinates b x
    left_inv := e.fromCoordinates_coordinates b x hx
    right_inv := e.coordinates_fromCoordinates b x hx }

/-- The actual vector solution with constant frame coefficients. -/
noncomputable def vectorSection (e : D.SolutionFrame) (b : D.domain)
    (c : D.solutionGerms (b : ℂ)) : ℂ → I → ℂ :=
  fun z => ∑ j, D.germValue b c j • e.solution j z

theorem analyticOnNhd_vectorSection (e : D.SolutionFrame) (b : D.domain)
    (c : D.solutionGerms (b : ℂ)) :
    AnalyticOnNhd ℂ (e.vectorSection b c) (Metric.ball e.center e.radius) :=
  Finset.univ.analyticOnNhd_fun_sum (fun j _ z hz =>
    (e.analytic j z hz).fun_const_smul (c := D.germValue b c j))

theorem ode_vectorSection (e : D.SolutionFrame) (b : D.domain)
    (c : D.solutionGerms (b : ℂ)) {z : ℂ} (hz : z ∈ Metric.ball e.center e.radius) :
    HasDerivAt (e.vectorSection b c) (D.matrix z *ᵥ e.vectorSection b c z) z := by
  simpa only [vectorSection, ← Matrix.mulVecLin_apply, map_sum, map_smul] using
    (HasDerivAt.fun_sum (u := Finset.univ)
      (fun j _ => (e.equation j z hz).fun_const_smul (D.germValue b c j)))

theorem value_vectorSection (e : D.SolutionFrame) (b : D.domain)
    (c : D.solutionGerms (b : ℂ)) (x : ℂ) :
    e.vectorSection b c x = e.matrix x *ᵥ D.germValue b c :=
  (e.matrix_mulVec x _).symm

theorem fromCoordinates_eq_vectorSection_germ (e : D.SolutionFrame) (b x : D.domain)
    (hx : x ∈ e.baseSet) (c : D.solutionGerms (b : ℂ)) :
    (e.fromCoordinates b x c : Germ (𝓝 (x : ℂ)) (I → ℂ)) = e.vectorSection b c := by
  have hode : ∀ᶠ z in 𝓝 (x : ℂ),
      HasDerivAt (e.vectorSection b c) (D.matrix z *ᵥ e.vectorSection b c z) z :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hx)
      (fun z hz => e.ode_vectorSection b c hz)
  have he : e.fromCoordinates b x c =
      D.solutionGermOfFun (e.vectorSection b c)
        (e.analyticOnNhd_vectorSection b c x hx) hode := by
    apply D.germValue_injective x.property
    rw [value_fromCoordinates, germValue_ofFun, value_vectorSection]
  exact congrArg Subtype.val he

theorem coordinates_change_eq (e e' : D.SolutionFrame) (b x y : D.domain)
    (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet)
    (hy : y ∈ e.baseSet) (hy' : y ∈ e'.baseSet) (c : D.solutionGerms (b : ℂ)) :
    e.coordinates b y (e'.fromCoordinates b y c) =
      e.coordinates b x (e'.fromCoordinates b x c) := by
  let d := e.coordinates b x (e'.fromCoordinates b x c)
  have hlocal : e'.vectorSection b c =ᶠ[𝓝 (x : ℂ)] e.vectorSection b d := by
    apply Germ.coe_eq.mp
    rw [← e'.fromCoordinates_eq_vectorSection_germ b x hx' c,
      ← e.fromCoordinates_eq_vectorSection_germ b x hx d]
    exact congrArg Subtype.val (e.fromCoordinates_coordinates b x hx _).symm
  have he := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      ((e'.analyticOnNhd_vectorSection b c).mono Set.inter_subset_right)
      ((e.analyticOnNhd_vectorSection b d).mono Set.inter_subset_left)
      ((convex_ball e.center e.radius).inter (convex_ball e'.center e'.radius)).isPreconnected
      (show (x : ℂ) ∈ Metric.ball e.center e.radius ∩ Metric.ball e'.center e'.radius
        from ⟨hx, hx'⟩) hlocal
  have hg : e'.fromCoordinates b y c = e.fromCoordinates b y d := by
    apply D.germValue_injective y.property
    rw [value_fromCoordinates, value_fromCoordinates,
      ← value_vectorSection, ← value_vectorSection]
    exact he ⟨hy, hy'⟩
  rw [hg, e.coordinates_fromCoordinates b y hy]

end SolutionFrame

end DirichletL.AnalyticMatrixODE

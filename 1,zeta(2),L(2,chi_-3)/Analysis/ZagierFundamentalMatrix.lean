import Analysis.ZagierODEExistence

/-!
Fundamental matrices for CDT v2 equation `explicitode`. Their invertibility
and comparison support the monodromy solution space in Lemma `14functions`.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- Columns are scalar solution states, with derivative orders indexing the rows. -/
noncomputable def zagierFundamentalMatrix (f : Fin 4 → ℂ → ℂ) (z : ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ := fun i j => zagierODEState (f j) z i

@[simp]
theorem zagierFundamentalMatrix_col (f : Fin 4 → ℂ → ℂ) (z : ℂ) (j : Fin 4) :
    (zagierFundamentalMatrix f z).col j = zagierODEState (f j) z := rfl

theorem zagierFundamentalMatrix_mulVec (f : Fin 4 → ℂ → ℂ) (z : ℂ) (c : Fin 4 → ℂ) :
    zagierFundamentalMatrix f z *ᵥ c = ∑ j, c j • zagierODEState (f j) z := by
  ext i
  simp [zagierFundamentalMatrix, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem zagierFundamentalMatrix_eq_one {f : Fin 4 → ℂ → ℂ} {z0 : ℂ}
    (hinit : ∀ j, zagierODEState (f j) z0 = Pi.single j 1) :
    zagierFundamentalMatrix f z0 = 1 := by
  ext i j
  simp [zagierFundamentalMatrix, hinit, Pi.single_apply, Matrix.one_apply, eq_comm]

theorem analyticOnNhd_zagierFundamentalMatrix {f : Fin 4 → ℂ → ℂ} {U : Set ℂ}
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U) :
    AnalyticOnNhd ℂ (zagierFundamentalMatrix f) U := by
  intro z hz
  apply analyticAt_pi_iff.mpr
  intro i
  apply analyticAt_pi_iff.mpr
  intro j
  exact analyticAt_pi_iff.mp (analyticOnNhd_zagierODEState (hf j) z hz) i

theorem hasDerivAt_zagierFundamentalMatrix {f : Fin 4 → ℂ → ℂ} {z : ℂ}
    (hf : ∀ j, AnalyticAt ℂ (f j) z) (hreg : z ∈ zagierODERegularSet)
    (hode : ∀ j, zagierAnalyticODE (f j) z = 0) :
    HasDerivAt (zagierFundamentalMatrix f)
      (zagierODECompanion z * zagierFundamentalMatrix f z) z := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hasDerivAt_pi.mp (hasDerivAt_zagierODEState_of_ode (hf j) hreg (hode j)) i

/-- Independence of scalar solutions makes their state matrix invertible throughout the domain. -/
theorem isUnit_zagierFundamentalMatrix {f : Fin 4 → ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hz : z ∈ U)
    (hreg : U ⊆ zagierODERegularSet) (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hode : ∀ j, Set.EqOn (zagierAnalyticODE (f j)) 0 U)
    (hli : LinearIndependent ℂ (fun j => fun z : U => f j z)) :
    IsUnit (zagierFundamentalMatrix f z) := by
  apply Matrix.linearIndependent_cols_iff_isUnit.mp
  exact linearIndependent_zagierODEState_initial hU hUc hz hreg hf hode hli

theorem det_zagierFundamentalMatrix_ne_zero {f : Fin 4 → ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hz : z ∈ U)
    (hreg : U ⊆ zagierODERegularSet) (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hode : ∀ j, Set.EqOn (zagierAnalyticODE (f j)) 0 U)
    (hli : LinearIndependent ℂ (fun j => fun z : U => f j z)) :
    (zagierFundamentalMatrix f z).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp
    (isUnit_zagierFundamentalMatrix hU hUc hz hreg hf hode hli)).ne_zero

theorem isUnit_zagierFundamentalMatrix_of_initial {f : Fin 4 → ℂ → ℂ} {U : Set ℂ} {z0 z : ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hz0 : z0 ∈ U) (hz : z ∈ U)
    (hreg : U ⊆ zagierODERegularSet) (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hode : ∀ j, Set.EqOn (zagierAnalyticODE (f j)) 0 U)
    (hinit : IsUnit (zagierFundamentalMatrix f z0)) :
    IsUnit (zagierFundamentalMatrix f z) := by
  apply isUnit_zagierFundamentalMatrix hU hUc hz hreg hf hode
  exact linearIndependent_of_zagierODEState_initial (hU.mem_nhds hz0)
    (fun j => hf j z0 hz0) (Matrix.linearIndependent_cols_iff_isUnit.mpr hinit)

theorem eventuallyEq_zagierODEState {f g : ℂ → ℂ} {z0 : ℂ} (h : f =ᶠ[𝓝 z0] g) :
    zagierODEState f =ᶠ[𝓝 z0] zagierODEState g := by
  have h1 := Filter.EventuallyEq.deriv h
  have h2 := Filter.EventuallyEq.deriv h1
  have h3 := Filter.EventuallyEq.deriv h2
  filter_upwards [h, h1, h2, h3] with z hz hz1 hz2 hz3
  ext i
  fin_cases i
  · exact hz
  · exact hz1
  · exact hz2
  · exact hz3

/-- Initial states give expansion coefficients in any invertible solution frame. -/
theorem eqOn_zagierODE_fundamental_expansion {f : Fin 4 → ℂ → ℂ} {g : ℂ → ℂ}
    {U : Set ℂ} {z0 : ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) (hz0 : z0 ∈ U)
    (hreg : z0 ∈ zagierODERegularSet) (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hfode : ∀ j, Set.EqOn (zagierAnalyticODE (f j)) 0 U)
    (hunit : IsUnit (zagierFundamentalMatrix f z0))
    (hg : AnalyticOnNhd ℂ g U) (hgode : Set.EqOn (zagierAnalyticODE g) 0 U) :
    Set.EqOn g (fun z => ∑ j,
      ((zagierFundamentalMatrix f z0)⁻¹ *ᵥ zagierODEState g z0) j • f j z) U := by
  let c := (zagierFundamentalMatrix f z0)⁻¹ *ᵥ zagierODEState g z0
  let F : ℂ → ℂ := fun z => ∑ j, c j • f j z
  have hF : AnalyticOnNhd ℂ F U :=
    Finset.univ.analyticOnNhd_sum (fun j _ z hz => (hf j z hz).const_smul (c := c j))
  have hFode : Set.EqOn (zagierAnalyticODE F) 0 U := by
    intro z hz
    rw [zagierAnalyticODE_sum (fun j => hf j z hz) c]
    simp only [hfode _ hz, smul_zero, Finset.sum_const_zero, Pi.zero_apply]
  apply eqOn_of_zagierAnalyticODE_initialState hU hUc hg hF hgode hFode hz0 hreg
  rw [zagierODEState_sum (fun j => hf j z0 hz0) c, ← zagierFundamentalMatrix_mulVec]
  simp only [c, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit), Matrix.one_mulVec]

theorem eqOn_zagierODEState_fundamental_expansion {f : Fin 4 → ℂ → ℂ} {g : ℂ → ℂ}
    {U : Set ℂ} {z0 : ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) (hz0 : z0 ∈ U)
    (hreg : z0 ∈ zagierODERegularSet) (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hfode : ∀ j, Set.EqOn (zagierAnalyticODE (f j)) 0 U)
    (hunit : IsUnit (zagierFundamentalMatrix f z0))
    (hg : AnalyticOnNhd ℂ g U) (hgode : Set.EqOn (zagierAnalyticODE g) 0 U) :
    Set.EqOn (zagierODEState g) (fun z => zagierFundamentalMatrix f z *ᵥ
      ((zagierFundamentalMatrix f z0)⁻¹ *ᵥ zagierODEState g z0)) U := by
  have he := eqOn_zagierODE_fundamental_expansion hU hUc hz0 hreg hf hfode hunit hg hgode
  intro z hz
  have hlocal := eventuallyEq_zagierODEState
    (Filter.eventually_of_mem (hU.mem_nhds hz) (fun w hw => he hw))
  simpa only [zagierODEState_sum (fun j => hf j z hz),
    zagierFundamentalMatrix_mulVec] using hlocal.self_of_nhds

/-- Solution frames differ by a constant right matrix on a connected comparison domain. -/
theorem eqOn_zagierFundamentalMatrix_comparison {f g : Fin 4 → ℂ → ℂ}
    {U : Set ℂ} {z0 : ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) (hz0 : z0 ∈ U)
    (hreg : z0 ∈ zagierODERegularSet) (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hfode : ∀ j, Set.EqOn (zagierAnalyticODE (f j)) 0 U)
    (hunit : IsUnit (zagierFundamentalMatrix f z0))
    (hg : ∀ j, AnalyticOnNhd ℂ (g j) U)
    (hgode : ∀ j, Set.EqOn (zagierAnalyticODE (g j)) 0 U) :
    Set.EqOn (zagierFundamentalMatrix g) (fun z => zagierFundamentalMatrix f z *
      ((zagierFundamentalMatrix f z0)⁻¹ * zagierFundamentalMatrix g z0)) U := by
  intro z hz
  ext i j
  exact congrFun (eqOn_zagierODEState_fundamental_expansion hU hUc hz0 hreg
    hf hfode hunit (hg j) (hgode j) hz) i

theorem eqOn_zagierFundamentalMatrix_transition {f g : Fin 4 → ℂ → ℂ}
    {U : Set ℂ} {z0 : ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) (hz0 : z0 ∈ U)
    (hreg : z0 ∈ zagierODERegularSet) (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hfode : ∀ j, Set.EqOn (zagierAnalyticODE (f j)) 0 U)
    (hunit : ∀ z ∈ U, IsUnit (zagierFundamentalMatrix f z))
    (hg : ∀ j, AnalyticOnNhd ℂ (g j) U)
    (hgode : ∀ j, Set.EqOn (zagierAnalyticODE (g j)) 0 U) :
    Set.EqOn (fun z => (zagierFundamentalMatrix f z)⁻¹ * zagierFundamentalMatrix g z)
      (fun _ => (zagierFundamentalMatrix f z0)⁻¹ * zagierFundamentalMatrix g z0) U := by
  have he := eqOn_zagierFundamentalMatrix_comparison hU hUc hz0 hreg
    hf hfode (hunit z0 hz0) hg hgode
  intro z hz
  dsimp only
  rw [he hz]
  exact Matrix.nonsing_inv_mul_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det _).mp (hunit z hz))

end DirichletL

import Analysis.AnalyticLinearODEExistence
import Analysis.ZagierODEUniqueness

/-!
Regular local solutions and a fundamental family for CDT v2 equation `explicitode`.
These supply the local solution space used in Lemma `14functions`.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The first three companion rows reconstruct the scalar derivative state. -/
theorem eventuallyEq_zagierODEState_of_companion {V : ℂ → Fin 4 → ℂ} {z0 : ℂ}
    (hV : ∀ᶠ z in 𝓝 z0, HasDerivAt V (zagierODECompanion z *ᵥ V z) z) :
    zagierODEState (fun z => V z 0) =ᶠ[𝓝 z0] V := by
  have hd (i : Fin 3) : deriv (fun z => V z i.castSucc) =ᶠ[𝓝 z0] fun z => V z i.succ := by
    filter_upwards [hV] with z hz
    have hi := (hasDerivAt_pi.mp hz i.castSucc).deriv
    fin_cases i <;> simpa [zagierODECompanion_mulVec] using hi
  have h1 := hd 0
  have h2 := (Filter.EventuallyEq.deriv h1).trans (hd 1)
  have h3 := (Filter.EventuallyEq.deriv h2).trans (hd 2)
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  ext i
  fin_cases i
  · rfl
  · exact hz1
  · exact hz2
  · exact hz3

/-- Every four initial derivative values occur in a local analytic solution at a regular point. -/
theorem exists_analytic_zagierODE {z0 : ℂ} (hreg : z0 ∈ zagierODERegularSet)
    (v : Fin 4 → ℂ) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f z0 ∧ zagierODEState f z0 = v ∧
      zagierAnalyticODE f =ᶠ[𝓝 z0] 0 := by
  obtain ⟨V, hV, hinit, hode⟩ := exists_analytic_matrix_ode
    (analyticOnNhd_zagierODECompanion z0 hreg) v
  have hf : AnalyticAt ℂ (fun z => V z 0) z0 := analyticAt_pi_iff.mp hV 0
  have hs := eventuallyEq_zagierODEState_of_companion hode
  refine ⟨fun z => V z 0, hf, hs.self_of_nhds.trans hinit, ?_⟩
  filter_upwards [hf.eventually_analyticAt, isOpen_zagierODERegularSet.mem_nhds hreg,
    hs, Filter.EventuallyEq.deriv hs, hode] with z hfz hz hsz hdsz hoz
  apply (zagierAnalyticODE_eq_zero_iff_hasDerivAt_state hfz hz).mpr
  have he : deriv (zagierODEState (fun z => V z 0)) z =
      zagierODECompanion z *ᵥ zagierODEState (fun z => V z 0) z := by
    rw [hdsz, hoz.deriv, hsz]
  rw [← he]
  exact (hasDerivAt_zagierODEState hfz).differentiableAt.hasDerivAt

private theorem eventuallyEq_deriv_sum {J : Type*} [Fintype J] {f : J → ℂ → ℂ} {z0 : ℂ}
    (hf : ∀ j, AnalyticAt ℂ (f j) z0) (c : J → ℂ) :
    deriv (fun z => ∑ j, c j • f j z) =ᶠ[𝓝 z0] fun z => ∑ j, c j • deriv (f j) z := by
  filter_upwards [Filter.eventually_all.mpr (fun j => (hf j).eventually_analyticAt)] with z hz
  exact (HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (hz j).differentiableAt.hasDerivAt.fun_const_smul (c j))).deriv

/-- The initial state is linear on finite families analytic at the base point. -/
theorem zagierODEState_sum {J : Type*} [Fintype J] {f : J → ℂ → ℂ} {z0 : ℂ}
    (hf : ∀ j, AnalyticAt ℂ (f j) z0) (c : J → ℂ) :
    zagierODEState (fun z => ∑ j, c j • f j z) z0 = ∑ j, c j • zagierODEState (f j) z0 := by
  have h1 := eventuallyEq_deriv_sum hf c
  have h2 := (Filter.EventuallyEq.deriv h1).trans
    (eventuallyEq_deriv_sum (fun j => (hf j).deriv) c)
  have h3 := (Filter.EventuallyEq.deriv h2).trans
    (eventuallyEq_deriv_sum (fun j => (hf j).deriv.deriv) c)
  ext i
  fin_cases i
  · simp [zagierODEState, Finset.sum_apply]
  · simpa [zagierODEState, Finset.sum_apply] using h1.self_of_nhds
  · simpa [zagierODEState, Finset.sum_apply] using h2.self_of_nhds
  · simpa [zagierODEState, Finset.sum_apply] using h3.self_of_nhds

/-- The polynomial ODE residual is linear on finite analytic families. -/
theorem zagierAnalyticODE_sum {J : Type*} [Fintype J] {f : J → ℂ → ℂ} {z0 : ℂ}
    (hf : ∀ j, AnalyticAt ℂ (f j) z0) (c : J → ℂ) :
    zagierAnalyticODE (fun z => ∑ j, c j • f j z) z0 =
      ∑ j, c j • zagierAnalyticODE (f j) z0 := by
  have h1 := eventuallyEq_deriv_sum hf c
  have h2 := (Filter.EventuallyEq.deriv h1).trans
    (eventuallyEq_deriv_sum (fun j => (hf j).deriv) c)
  have h3 := (Filter.EventuallyEq.deriv h2).trans
    (eventuallyEq_deriv_sum (fun j => (hf j).deriv.deriv) c)
  have h4 := (Filter.EventuallyEq.deriv h3).trans
    (eventuallyEq_deriv_sum (fun j => (hf j).deriv.deriv.deriv) c)
  simp only [zagierAnalyticODE]
  rw [h1.self_of_nhds, h2.self_of_nhds, h3.self_of_nhds, h4.self_of_nhds]
  simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Independent derivative states force independence on every neighborhood of the base point. -/
theorem linearIndependent_of_zagierODEState_initial {J : Type*} [Fintype J]
    {f : J → ℂ → ℂ} {U : Set ℂ} {z0 : ℂ} (hU : U ∈ 𝓝 z0)
    (hf : ∀ j, AnalyticAt ℂ (f j) z0)
    (hli : LinearIndependent ℂ (fun j => zagierODEState (f j) z0)) :
    LinearIndependent ℂ (fun j => fun z : U => f j z) := by
  classical
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc
  have h0 : (fun z => ∑ j, c j • f j z) =ᶠ[𝓝 z0] 0 := by
    filter_upwards [hU] with z hz
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] using
      congrFun hc (⟨z, hz⟩ : U)
  have h1 := Filter.EventuallyEq.deriv h0
  have h2 := Filter.EventuallyEq.deriv h1
  have h3 := Filter.EventuallyEq.deriv h2
  apply hli c
  rw [← zagierODEState_sum hf c]
  ext i
  fin_cases i
  · simpa [zagierODEState] using h0.self_of_nhds
  · simpa [zagierODEState] using h1.self_of_nhds
  · simpa [zagierODEState] using h2.self_of_nhds
  · simpa [zagierODEState] using h3.self_of_nhds

/-- Four normalized independent analytic solutions exist on a regular ball. -/
theorem exists_zagierODE_fundamental_solutions {z0 : ℂ} (hreg : z0 ∈ zagierODERegularSet) :
    ∃ (r : ℝ) (f : Fin 4 → ℂ → ℂ), 0 < r ∧ Metric.ball z0 r ⊆ zagierODERegularSet ∧
      (∀ j, AnalyticOnNhd ℂ (f j) (Metric.ball z0 r)) ∧
      (∀ j, Set.EqOn (zagierAnalyticODE (f j)) 0 (Metric.ball z0 r)) ∧
      (∀ j, zagierODEState (f j) z0 = Pi.single j 1) ∧
      LinearIndependent ℂ (fun j => fun z : Metric.ball z0 r => f j z) := by
  classical
  choose f hf hinit hode using
    (fun j : Fin 4 => exists_analytic_zagierODE hreg (Pi.single j 1))
  have hall : ∀ᶠ z in 𝓝 z0, z ∈ zagierODERegularSet ∧
      ∀ j, AnalyticAt ℂ (f j) z ∧ zagierAnalyticODE (f j) z = 0 := by
    filter_upwards [isOpen_zagierODERegularSet.mem_nhds hreg,
      Filter.eventually_all.mpr (fun j => (hf j).eventually_analyticAt.and (hode j))]
      with z hz hzs
    exact ⟨hz, hzs⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hall
  refine ⟨r, f, hr, fun z hz => (hball z hz).1,
    fun j z hz => (hball z hz).2 j |>.1,
    fun j z hz => (hball z hz).2 j |>.2, hinit, ?_⟩
  apply linearIndependent_of_zagierODEState_initial (Metric.ball_mem_nhds z0 hr) hf
  simpa only [hinit] using Pi.linearIndependent_single_one (Fin 4) ℂ

/-- A normalized fundamental family spans all analytic solutions on the connected domain. -/
theorem eqOn_zagierODE_initialState_expansion {f : Fin 4 → ℂ → ℂ} {g : ℂ → ℂ}
    {U : Set ℂ} {z0 : ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) (hz0 : z0 ∈ U)
    (hreg : z0 ∈ zagierODERegularSet) (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hfode : ∀ j, Set.EqOn (zagierAnalyticODE (f j)) 0 U)
    (hinit : ∀ j, zagierODEState (f j) z0 = Pi.single j 1)
    (hg : AnalyticOnNhd ℂ g U) (hgode : Set.EqOn (zagierAnalyticODE g) 0 U) :
    Set.EqOn g (fun z => ∑ j, zagierODEState g z0 j • f j z) U := by
  let c := zagierODEState g z0
  let F : ℂ → ℂ := fun z => ∑ j, c j • f j z
  have hF : AnalyticOnNhd ℂ F U :=
    Finset.univ.analyticOnNhd_sum (fun j _ z hz => (hf j z hz).const_smul (c := c j))
  have hFode : Set.EqOn (zagierAnalyticODE F) 0 U := by
    intro z hz
    rw [zagierAnalyticODE_sum (fun j => hf j z hz) c]
    simp only [hfode _ hz, smul_zero, Finset.sum_const_zero, Pi.zero_apply]
  apply eqOn_of_zagierAnalyticODE_initialState hU hUc hg hF hgode hFode hz0 hreg
  rw [zagierODEState_sum (fun j => hf j z0 hz0) c]
  ext i
  simp [hinit, Finset.sum_apply, Pi.single_apply, c]

end DirichletL

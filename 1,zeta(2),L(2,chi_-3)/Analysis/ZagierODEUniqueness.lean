import Analysis.AnalyticLinearODE
import Analysis.ZagierCompanionSystem

/-!
Uniqueness from regular initial data for CDT v2 equation `explicitode`.
This is part of the solution-space argument in Lemma `14functions`;
existence of continuations and monodromy is not assumed here.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem analyticAt_state {f : ℂ → ℂ} {z0 : ℂ} (hf : AnalyticAt ℂ f z0) :
    AnalyticAt ℂ (zagierODEState f) z0 := by
  apply analyticAt_pi_iff.mpr
  intro i
  fin_cases i
  · exact hf
  · exact hf.deriv
  · exact hf.deriv.deriv
  · exact hf.deriv.deriv.deriv

private theorem eventually_hasDerivAt_state {f : ℂ → ℂ} {z0 : ℂ}
    (hf : AnalyticAt ℂ f z0) (hreg : z0 ∈ zagierODERegularSet)
    (hode : zagierAnalyticODE f =ᶠ[𝓝 z0] 0) :
    ∀ᶠ z in 𝓝 z0,
      HasDerivAt (zagierODEState f) (zagierODECompanion z *ᵥ zagierODEState f z) z := by
  filter_upwards [hf.eventually_analyticAt, isOpen_zagierODERegularSet.mem_nhds hreg,
    hode] with z hfz hz hoz
  exact hasDerivAt_zagierODEState_of_ode hfz hz hoz

/-- The first four initial values determine an analytic solution germ at a regular point. -/
theorem eventuallyEq_of_zagierAnalyticODE {f g : ℂ → ℂ} {z0 : ℂ}
    (hf : AnalyticAt ℂ f z0) (hg : AnalyticAt ℂ g z0) (hreg : z0 ∈ zagierODERegularSet)
    (hinit : zagierODEState f z0 = zagierODEState g z0)
    (hfode : zagierAnalyticODE f =ᶠ[𝓝 z0] 0)
    (hgode : zagierAnalyticODE g =ᶠ[𝓝 z0] 0) : f =ᶠ[𝓝 z0] g := by
  have hs := eventuallyEq_of_analytic_matrix_ode
    (analyticOnNhd_zagierODECompanion z0 hreg).continuousAt
    (analyticAt_state hf) (analyticAt_state hg) hinit
    (eventually_hasDerivAt_state hf hreg hfode) (eventually_hasDerivAt_state hg hreg hgode)
  filter_upwards [hs] with z hz
  exact congrFun hz (0 : Fin 4)

/-- Equal regular initial data give equal solutions on an open connected domain. -/
theorem eqOn_of_zagierAnalyticODE_initialState {f g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hfode : Set.EqOn (zagierAnalyticODE f) 0 U)
    (hgode : Set.EqOn (zagierAnalyticODE g) 0 U) {z0 : ℂ} (hz0 : z0 ∈ U)
    (hreg : z0 ∈ zagierODERegularSet)
    (hinit : zagierODEState f z0 = zagierODEState g z0) : Set.EqOn f g U := by
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg hUc hz0
  apply eventuallyEq_of_zagierAnalyticODE (hf z0 hz0) (hg z0 hz0) hreg hinit
  · filter_upwards [hU.mem_nhds hz0] with z hz
    exact hfode hz
  · filter_upwards [hU.mem_nhds hz0] with z hz
    exact hgode hz

/-- The actual Zagier solution cannot have all four initial values zero at a regular point. -/
theorem zagierODEState_symmetrizedAnalytic_hA_ne_zero {z : ℂ}
    (hz : ‖z‖ < 1 / 648) (hreg : z ∈ zagierODERegularSet) :
    zagierODEState (symmetrizedAnalytic hA) z ≠ 0 := by
  intro hzero
  have hf : AnalyticOnNhd ℂ (symmetrizedAnalytic hA) (Metric.ball 0 (1 / 648)) := by
    intro x hx
    exact analyticAt_symmetrizedAnalytic_hA
      (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
  have hode : Set.EqOn (zagierAnalyticODE (symmetrizedAnalytic hA)) 0
      (Metric.ball 0 (1 / 648)) := by
    intro x hx
    exact zagierAnalyticODE_symmetrizedAnalytic_hA
      (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
  have he := eqOn_of_zagierAnalyticODE_initialState (g := 0) Metric.isOpen_ball
    (convex_ball (0 : ℂ) (1 / 648)).isPreconnected hf analyticOnNhd_const hode
    (by intro x hx; simp [zagierAnalyticODE])
    (by simpa only [Metric.mem_ball, dist_zero_right] using hz) hreg
    (by rw [hzero]; ext i; fin_cases i <;> simp [zagierODEState])
  have he0 := he (show (0 : ℂ) ∈ Metric.ball 0 (1 / 648) by
    simp only [Metric.mem_ball, dist_self]; norm_num)
  norm_num [symmetrizedAnalytic_hA_zero] at he0

/-- Independent scalar solutions have independent initial states at a regular point. -/
theorem linearIndependent_zagierODEState_initial {J : Type*} [Fintype J]
    {f : J → ℂ → ℂ} {U : Set ℂ} {z0 : ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hz0 : z0 ∈ U)
    (hreg : U ⊆ zagierODERegularSet) (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hode : ∀ j, Set.EqOn (zagierAnalyticODE (f j)) 0 U)
    (hli : LinearIndependent ℂ (fun j => fun z : U => f j z)) :
    LinearIndependent ℂ (fun j => zagierODEState (f j) z0) := by
  classical
  apply (linearIndependent_iff_initialValue_of_analytic_matrix_ode hU hUc hz0
    (analyticOnNhd_zagierODECompanion z0 (hreg hz0)).continuousAt
    (fun j => analyticOnNhd_zagierODEState (hf j))
    (fun j z hz => hasDerivAt_zagierODEState_of_ode (hf j z hz) (hreg hz) (hode j hz))).mp
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc
  apply hli c
  funext z
  have he := congrFun (congrFun hc z) (0 : Fin 4)
  simpa [Finset.sum_apply, zagierODEState] using he

/-- A finite independent family of analytic solutions of `explicitode` has at most four members. -/
theorem card_le_four_of_zagierAnalyticODE {J : Type*} [Fintype J]
    {f : J → ℂ → ℂ} {U : Set ℂ} {z0 : ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hz0 : z0 ∈ U)
    (hreg : U ⊆ zagierODERegularSet) (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hode : ∀ j, Set.EqOn (zagierAnalyticODE (f j)) 0 U)
    (hli : LinearIndependent ℂ (fun j => fun z : U => f j z)) : Fintype.card J ≤ 4 := by
  simpa only [Module.finrank_pi, Fintype.card_fin] using
    (linearIndependent_zagierODEState_initial hU hUc hz0 hreg hf hode hli).fintype_card_le_finrank

end DirichletL

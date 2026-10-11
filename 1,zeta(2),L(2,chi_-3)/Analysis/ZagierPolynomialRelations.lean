import Analysis.ZagierSolutionFrames

/-!
Polynomial differential relations on homogeneous Zagier solution germs.
CDT v2, proof of Lemma `14functions`, propagates such relations through
monodromy before comparing the derivative coefficients in `remaining`.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

/-- A polynomial relation among the function and its first three derivatives. -/
noncomputable def zagierPolynomialResidual (P : Fin 4 → Polynomial ℂ)
    (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ i, (P i).eval z * zagierODEState f z i

theorem analyticOnNhd_zagierPolynomialResidual (P : Fin 4 → Polynomial ℂ)
    {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) :
    AnalyticOnNhd ℂ (zagierPolynomialResidual P f) U := by
  apply Finset.univ.analyticOnNhd_fun_sum
  intro i _ z hz
  exact ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (P i)) z (Set.mem_univ z)).mul
    ((analyticOnNhd_pi_iff.mp (analyticOnNhd_zagierODEState hf) i) z hz)

theorem eventuallyEq_zagierPolynomialResidual (P : Fin 4 → Polynomial ℂ)
    {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    zagierPolynomialResidual P f =ᶠ[𝓝 z] zagierPolynomialResidual P g := by
  filter_upwards [eventuallyEq_zagierODEState h] with x hx
  simp only [zagierPolynomialResidual, hx]

theorem zagierPolynomialResidual_add (P : Fin 4 → Polynomial ℂ)
    {f g : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) :
    zagierPolynomialResidual P (f + g) z =
      zagierPolynomialResidual P f z + zagierPolynomialResidual P g z := by
  simp only [zagierPolynomialResidual, zagierODEState_add hf hg, Pi.add_apply,
    mul_add, Finset.sum_add_distrib]

theorem zagierPolynomialResidual_smul (P : Fin 4 → Polynomial ℂ)
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (c : ℂ) :
    zagierPolynomialResidual P (c • f) z = c • zagierPolynomialResidual P f z := by
  simp only [zagierPolynomialResidual, zagierODEState_smul hf, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem zagierPolynomialResidual_eqOn_of_preconnected (P : Fin 4 → Polynomial ℂ)
    {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hU : IsPreconnected U) {z : ℂ} (hz : z ∈ U)
    (h : zagierPolynomialResidual P f =ᶠ[𝓝 z] 0) :
    Set.EqOn (zagierPolynomialResidual P f) 0 U :=
  (analyticOnNhd_zagierPolynomialResidual P hf).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hU hz h

/-- Locality descends the polynomial residual to canonical function germs. -/
noncomputable def zagierPolynomialResidualGerm (P : Fin 4 → Polynomial ℂ)
    (z : ℂ) (φ : Germ (𝓝 z) ℂ) : Germ (𝓝 z) ℂ :=
  φ.liftOn (fun f => (zagierPolynomialResidual P f : Germ (𝓝 z) ℂ))
    (fun _ _ h => Germ.coe_eq.mpr (eventuallyEq_zagierPolynomialResidual P h))

@[simp]
theorem zagierPolynomialResidualGerm_coe (P : Fin 4 → Polynomial ℂ)
    (z : ℂ) (f : ℂ → ℂ) :
    zagierPolynomialResidualGerm P z f = (zagierPolynomialResidual P f : Germ (𝓝 z) ℂ) := rfl

/-- The residual is complex-linear on homogeneous analytic solution germs. -/
noncomputable def zagierPolynomialRelationMap (P : Fin 4 → Polynomial ℂ) (z : ℂ) :
    zagierSolutionGerms z →ₗ[ℂ] Germ (𝓝 z) ℂ where
  toFun φ := zagierPolynomialResidualGerm P z φ
  map_add' φ ψ := by
    obtain ⟨f, hf, _, hφ⟩ := φ.property
    obtain ⟨g, hg, _, hψ⟩ := ψ.property
    change zagierPolynomialResidualGerm P z (φ.val + ψ.val) =
      zagierPolynomialResidualGerm P z φ.val + zagierPolynomialResidualGerm P z ψ.val
    rw [← hφ, ← hψ, ← Germ.coe_add]
    change (zagierPolynomialResidual P (f + g) : Germ (𝓝 z) ℂ) =
      (zagierPolynomialResidual P f : Germ (𝓝 z) ℂ) + zagierPolynomialResidual P g
    rw [← Germ.coe_add]
    apply Germ.coe_eq.mpr
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with x hfx hgx
    exact zagierPolynomialResidual_add P hfx hgx
  map_smul' c φ := by
    obtain ⟨f, hf, _, hφ⟩ := φ.property
    change zagierPolynomialResidualGerm P z (c • φ.val) =
      c • zagierPolynomialResidualGerm P z φ.val
    rw [← hφ, ← Germ.coe_smul]
    change (zagierPolynomialResidual P (c • f) : Germ (𝓝 z) ℂ) =
      c • (zagierPolynomialResidual P f : Germ (𝓝 z) ℂ)
    rw [← Germ.coe_smul]
    apply Germ.coe_eq.mpr
    filter_upwards [hf.eventually_analyticAt] with x hfx
    exact zagierPolynomialResidual_smul P hfx c

@[simp]
theorem zagierPolynomialRelationMap_apply (P : Fin 4 → Polynomial ℂ) (z : ℂ)
    (φ : zagierSolutionGerms z) :
    zagierPolynomialRelationMap P z φ = zagierPolynomialResidualGerm P z φ := rfl

/-- Solution germs satisfying one polynomial differential relation. -/
noncomputable def zagierPolynomialRelationSubmodule (P : Fin 4 → Polynomial ℂ) (z : ℂ) :
    Submodule ℂ (zagierSolutionGerms z) := LinearMap.ker (zagierPolynomialRelationMap P z)

theorem mem_zagierPolynomialRelationSubmodule_iff (P : Fin 4 → Polynomial ℂ) {z : ℂ}
    (φ : zagierSolutionGerms z) {f : ℂ → ℂ} (hφ : (φ : Germ (𝓝 z) ℂ) = f) :
    φ ∈ zagierPolynomialRelationSubmodule P z ↔ zagierPolynomialResidual P f =ᶠ[𝓝 z] 0 := by
  change zagierPolynomialResidualGerm P z φ.val = 0 ↔ _
  rw [hφ]
  exact Germ.coe_eq

/-- No nonzero relation of order at most three annihilates the entire regular solution space. -/
theorem zagierPolynomialRelationSubmodule_eq_top_iff (b : zagierODERegularSet)
    (P : Fin 4 → Polynomial ℂ) :
    zagierPolynomialRelationSubmodule P (b : ℂ) = ⊤ ↔ P = 0 := by
  constructor
  · intro h
    let e := ZagierSolutionFrame.atPoint b
    have hb : (b : ℂ) ∈ Metric.ball e.center e.radius :=
      ZagierSolutionFrame.mem_baseSet_atPoint b
    have hrel (j : Fin 4) : zagierPolynomialResidual P (e.solution j) =ᶠ[𝓝 (b : ℂ)] 0 := by
      have ho : zagierAnalyticODE (e.solution j) =ᶠ[𝓝 (b : ℂ)] 0 :=
        Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hb)
          (fun z hz => e.equation j hz)
      have hm : zagierSolutionGermOfFun (e.solution j) (e.analytic j b hb) ho ∈
          zagierPolynomialRelationSubmodule P (b : ℂ) := by
        rw [h]
        exact Submodule.mem_top
      exact (mem_zagierPolynomialRelationSubmodule_iff P _ rfl).mp hm
    have hall : ∀ᶠ z in 𝓝 (b : ℂ), ∀ i, (P i).eval z = 0 := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hb, eventually_all.mpr hrel] with z hz hr
      have hv : (fun i => (P i).eval z) ᵥ* zagierFundamentalMatrix e.solution z = 0 := by
        funext j
        exact hr j
      have ha : (fun i => (P i).eval z) = (0 : Fin 4 → ℂ) := by
        apply Matrix.vecMul_injective_of_isUnit (e.isUnit_matrix hz)
        simpa only [Matrix.zero_vecMul] using hv
      intro i
      exact congrFun ha i
    funext i
    apply Polynomial.funext
    have hi : (fun z => (P i).eval z) =ᶠ[𝓝 (b : ℂ)] 0 := hall.mono (fun z hz => hz i)
    have hp := AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (P i)
    have he := hp.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ (b : ℂ)) hi
    intro z
    simpa only [Pi.zero_apply, Polynomial.eval_zero] using he (Set.mem_univ z)
  · rintro rfl
    apply Submodule.eq_top_iff'.mpr
    intro φ
    obtain ⟨f, _, _, hφ⟩ := φ.property
    apply (mem_zagierPolynomialRelationSubmodule_iff 0 φ hφ.symm).mpr
    exact Filter.Eventually.of_forall (fun z => by simp [zagierPolynomialResidual])

end DirichletL

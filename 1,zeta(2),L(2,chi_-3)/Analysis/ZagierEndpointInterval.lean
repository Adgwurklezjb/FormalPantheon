import Analysis.ZagierPullbackRegularity
import Analysis.ZagierPullbackTransport

/-!
Regular paths joining the endpoint-solution coordinates for CDT v2's
monodromy step in `14functions`, under the coordinate `y in x`.
-/

namespace DirichletL

open Filter Set unitInterval
open scoped Topology

theorem mobiusCoordinate_ofReal (r : ℝ) :
    mobiusCoordinate r = ((r + r / (r - 1) : ℝ) : ℂ) := by
  simp [mobiusCoordinate]

theorem mobiusCoordinate_mem_Ioo {r : ℝ} (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) :
    r + r / (r - 1) ∈ Ioo (-1 / 72 : ℝ) 0 := by
  have hd : r - 1 < 0 := by linarith [hr.2]
  have he : r + r / (r - 1) = r ^ 2 / (r - 1) := by
    field_simp [ne_of_lt hd]
    ring
  rw [he]
  refine ⟨(lt_div_iff_of_neg hd).mpr ?_, div_neg_of_pos_of_neg (sq_pos_of_pos hr.1) hd⟩
  have hprod : (9 * r - 1) * (8 * r + 1) < 0 :=
    mul_neg_of_neg_of_pos (by linarith [hr.2]) (by linarith [hr.1])
  nlinarith

theorem zagierEndpointInterval_noncritical {r : ℝ} (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) :
    (r : ℂ) ≠ 0 ∧ (r : ℂ) ≠ 1 ∧ (r : ℂ) ≠ 2 := by
  refine ⟨by exact_mod_cast ne_of_gt hr.1, ?_, ?_⟩
  · exact_mod_cast (by linarith [hr.2] : r ≠ 1)
  · exact_mod_cast (by linarith [hr.2] : r ≠ 2)

theorem mobiusCoordinate_regular_of_mem_Ioo {r : ℝ} (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) :
    mobiusCoordinate r ∈ zagierODERegularSet := by
  rw [mobiusCoordinate_ofReal]
  let y : ℝ := r + r / (r - 1)
  have hy : y ∈ Ioo (-1 / 72 : ℝ) 0 := mobiusCoordinate_mem_Ioo hr
  apply (mem_zagierODERegularSet_iff _).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast ne_of_lt hy.2
  · exact_mod_cast (by linarith [hy.2] : y ≠ 4)
  · exact_mod_cast ne_of_gt hy.1
  · have hy₃ : y ^ 3 ≤ 0 := by
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hy.2.le (sq_nonneg y)]
    have hneg : -1 + 118 * y - 122 * y ^ 2 + 144 * y ^ 3 < 0 := by
      nlinarith [sq_nonneg y]
    have he : zagierSingularCubic.eval (y : ℂ) =
        ((-1 + 118 * y - 122 * y ^ 2 + 144 * y ^ 3 : ℝ) : ℂ) := by
      simp [zagierSingularCubic]
    rw [he]
    exact_mod_cast ne_of_lt hneg

theorem zagierEndpointInterval_solutions {r : ℝ} (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) :
    AnalyticAt ℂ zagierAnalytic (r : ℂ) ∧
      zagierSecondOrderODE zagierAnalytic =ᶠ[𝓝 (r : ℂ)] 0 ∧
        AnalyticAt ℂ zagierEndpointSolution (r : ℂ) ∧
          zagierSecondOrderODE zagierEndpointSolution =ᶠ[𝓝 (r : ℂ)] 0 := by
  have hnorm : ‖(r : ℂ)‖ < 1 / 9 := by simpa [abs_of_pos hr.1] using hr.2
  have hr₁ := (zagierEndpointInterval_noncritical hr).2.1
  have ht : ‖zagierEndpointCoordinate r‖ < 1 / 9 := by
    rw [zagierEndpointCoordinate_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (zagierEndpointCoordinate_mem_Ioo hr).1]
    exact (zagierEndpointCoordinate_mem_Ioo hr).2
  refine ⟨analyticAt_zagierAnalytic hnorm, ?_, analyticAt_zagierEndpointSolution hr₁ ht, ?_⟩
  · filter_upwards [continuous_norm.continuousAt.eventually_lt_const hnorm] with z hz
    exact zagierAnalytic_ode hz
  · filter_upwards [eventually_ne_nhds hr₁,
      (analyticAt_zagierEndpointCoordinate hr₁).continuousAt.norm.eventually_lt_const ht]
      with z hz htz
    exact zagierEndpointSolution_ode hz htz

/-- A path joining two interior real points while staying in the same interval. -/
noncomputable def zagierEndpointRealPath {r s : ℝ}
    (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) (hs : s ∈ Ioo 0 (1 / 9 : ℝ)) : Path r s :=
  (((convex_Ioo (0 : ℝ) (1 / 9)).isPathConnected ⟨r, hr⟩).joinedIn r hr s hs).somePath

theorem zagierEndpointRealPath_mem {r s : ℝ}
    (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) (hs : s ∈ Ioo 0 (1 / 9 : ℝ)) (t : I) :
    zagierEndpointRealPath hr hs t ∈ Ioo 0 (1 / 9 : ℝ) :=
  (((convex_Ioo (0 : ℝ) (1 / 9)).isPathConnected ⟨r, hr⟩).joinedIn r hr s hs).somePath_mem t

/-- The projected regular path used to compare the two named endpoint solutions. -/
noncomputable def zagierEndpointPath {r s : ℝ}
    (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) (hs : s ∈ Ioo 0 (1 / 9 : ℝ)) :
    Path (⟨mobiusCoordinate r, mobiusCoordinate_regular_of_mem_Ioo hr⟩ : zagierODERegularSet)
      ⟨mobiusCoordinate s, mobiusCoordinate_regular_of_mem_Ioo hs⟩ :=
  zagierMobiusPath ((zagierEndpointRealPath hr hs).map Complex.continuous_ofReal)
    (fun t => (zagierEndpointInterval_noncritical (zagierEndpointRealPath_mem hr hs t)).2.1)
    (fun t => mobiusCoordinate_regular_of_mem_Ioo (zagierEndpointRealPath_mem hr hs t))

@[simp]
theorem zagierEndpointPath_apply {r s : ℝ}
    (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) (hs : s ∈ Ioo 0 (1 / 9 : ℝ)) (t : I) :
    (zagierEndpointPath hr hs t : ℂ) = mobiusCoordinate (zagierEndpointRealPath hr hs t) := rfl

theorem mobiusGermPullback_zagierEndpointPath (b : zagierODERegularSet) {r s : ℝ}
    (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) (hs : s ∈ Ioo 0 (1 / 9 : ℝ)) {f : ℂ → ℂ}
    (hf : ∀ u : ℝ, u ∈ Ioo 0 (1 / 9 : ℝ) → AnalyticAt ℂ f (u : ℂ))
    (hE : ∀ u : ℝ, u ∈ Ioo 0 (1 / 9 : ℝ) → zagierSecondOrderODE f =ᶠ[𝓝 (u : ℂ)] 0)
    (φ : zagierSolutionGerms (mobiusCoordinate r))
    (hφ : mobiusGermPullback (zagierEndpointInterval_noncritical hr).2.1
      (φ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = f) :
    mobiusGermPullback (zagierEndpointInterval_noncritical hs).2.1
      (zagierPathTransport b (zagierEndpointPath hr hs) φ :
        Germ (𝓝 (mobiusCoordinate s)) ℂ) = f := by
  let δ := (zagierEndpointRealPath hr hs).map Complex.continuous_ofReal
  apply mobiusGermPullback_zagierPathTransport b δ _ _ _ _
    (AnalyticContinuationAlong.const δ.continuous (fun t =>
      hf _ (zagierEndpointRealPath_mem hr hs t)))
    (fun t => hE _ (zagierEndpointRealPath_mem hr hs t))
    (fun t => (zagierEndpointInterval_noncritical (zagierEndpointRealPath_mem hr hs t)).1)
    (fun t => (zagierEndpointInterval_noncritical (zagierEndpointRealPath_mem hr hs t)).2.2) φ hφ

theorem exists_zagierEndpointSolutionGerms {r : ℝ} (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) :
    ∃ φ ψ : zagierSolutionGerms (mobiusCoordinate r),
      mobiusGermPullback (zagierEndpointInterval_noncritical hr).2.1
        (φ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = zagierAnalytic ∧
      mobiusGermPullback (zagierEndpointInterval_noncritical hr).2.1
        (ψ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = zagierEndpointSolution ∧
      LinearIndependent ℂ ![φ, ψ] := by
  obtain ⟨hr₀, hr₁, hr₂⟩ := zagierEndpointInterval_noncritical hr
  obtain ⟨hH, hHo, hS, hSo⟩ := zagierEndpointInterval_solutions hr
  obtain ⟨φ, hφ⟩ := exists_zagierSolutionGerm_mobiusPullback hr₀ hr₁ hr₂ hH hHo
  obtain ⟨ψ, hψ⟩ := exists_zagierSolutionGerm_mobiusPullback hr₀ hr₁ hr₂ hS hSo
  refine ⟨φ, ψ, hφ, hψ, Fintype.linearIndependent_iff.mpr ?_⟩
  intro a ha i
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at ha
  have he := congrArg (fun u : zagierSolutionGerms (mobiusCoordinate r) =>
    mobiusGermPullback hr₁ (u : Germ (𝓝 (mobiusCoordinate r)) ℂ)) ha
  simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero,
    map_add, map_smul, map_zero, hφ, hψ] at he
  have hz := eq_zero_of_zagierEndpointSolution_relation hr (Germ.coe_eq.mp he)
  fin_cases i
  · exact hz.1
  · exact hz.2

end DirichletL

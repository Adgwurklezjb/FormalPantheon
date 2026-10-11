import Analysis.AnalyticContinuation
import Analysis.AnalyticPrimitives

/-!
Normalized local logarithm branches and their continuation along exponential
lifts, used for the local monodromy of CDT v2 equation `zagr`.
-/

namespace DirichletL

open Filter Set
open scoped Topology

/-- The logarithm branch with value `w` at `exp w`. -/
noncomputable def complexLogarithmBranch (w z : ℂ) : ℂ :=
  w + Complex.log (z / Complex.exp w)

@[simp] theorem complexLogarithmBranch_self (w : ℂ) :
    complexLogarithmBranch w (Complex.exp w) = w := by
  simp [complexLogarithmBranch, Complex.exp_ne_zero]

theorem analyticAt_complexLogarithmBranch {w z : ℂ}
    (hz : z / Complex.exp w ∈ Complex.slitPlane) :
    AnalyticAt ℂ (complexLogarithmBranch w) z :=
  analyticAt_const.add ((analyticAt_id.div analyticAt_const (Complex.exp_ne_zero w)).clog hz)

theorem hasDerivAt_complexLogarithmBranch {w z : ℂ}
    (hz : z / Complex.exp w ∈ Complex.slitPlane) :
    HasDerivAt (complexLogarithmBranch w) z⁻¹ z := by
  have hz₀ : z ≠ 0 := by
    intro he
    exact Complex.slitPlane_ne_zero hz (by simp [he])
  convert (((hasDerivAt_id z).div_const (Complex.exp w)).clog hz).const_add w using 1
  simp only [id_eq]
  field_simp [Complex.exp_ne_zero, hz₀]

theorem eventuallyEq_complexLogarithmBranch {v w : ℂ}
    (hvw : (v - w).im ∈ Ioo (-Real.pi) Real.pi) :
    complexLogarithmBranch v =ᶠ[𝓝 (Complex.exp v)] complexLogarithmBranch w := by
  have hv : Complex.exp v / Complex.exp v ∈ Complex.slitPlane := by
    simp [Complex.exp_ne_zero]
  have hw : Complex.exp v / Complex.exp w ∈ Complex.slitPlane := by
    rw [← Complex.exp_sub]
    exact Complex.expPartialHomeomorph.map_source' hvw
  have hn (u : ℂ) (hu : Complex.exp v / Complex.exp u ∈ Complex.slitPlane) :
      ∀ᶠ z in 𝓝 (Complex.exp v), z / Complex.exp u ∈ Complex.slitPlane :=
    (continuous_id.div_const (Complex.exp u)).continuousAt.preimage_mem_nhds
      (Complex.isOpen_slitPlane.mem_nhds hu)
  have hd : ∀ᶠ z in 𝓝 (Complex.exp v),
      HasDerivAt (fun z => complexLogarithmBranch v z - complexLogarithmBranch w z) 0 z := by
    filter_upwards [hn v hv, hn w hw] with z hzv hzw
    simpa only [sub_self] using
      (hasDerivAt_complexLogarithmBranch hzv).sub (hasDerivAt_complexLogarithmBranch hzw)
  have he := eventuallyEq_const_of_eventually_hasDerivAt_zero hd
  have hinit : complexLogarithmBranch w (Complex.exp v) = v := by
    rw [complexLogarithmBranch, ← Complex.exp_sub, Complex.log_exp hvw.1 hvw.2.le]
    ring
  filter_upwards [he] with z hz
  simpa only [complexLogarithmBranch_self, hinit, sub_self, sub_eq_zero] using hz

theorem analyticContinuationAlong_complexLogarithmBranch {T : Type*} [TopologicalSpace T]
    {w : T → ℂ} (hw : Continuous w) :
    AnalyticContinuationAlong (fun t => Complex.exp (w t)) (fun t => complexLogarithmBranch (w t)) := by
  refine ⟨Complex.continuous_exp.comp hw, ?_, ?_⟩
  · intro t
    exact analyticAt_complexLogarithmBranch (by simp [Complex.exp_ne_zero])
  · intro t
    have hn : ∀ᶠ s in 𝓝 t, (w s - w t).im ∈ Ioo (-Real.pi) Real.pi :=
      (Complex.continuous_im.comp (hw.sub continuous_const)).continuousAt.preimage_mem_nhds
        (Ioo_mem_nhds (by simpa using neg_neg_of_pos Real.pi_pos)
          (by simpa using Real.pi_pos))
    filter_upwards [hn] with s hs
    exact eventuallyEq_complexLogarithmBranch hs

theorem complexLogarithmBranch_add_period (w z : ℂ) :
    complexLogarithmBranch (w + 2 * Real.pi * Complex.I) z =
      complexLogarithmBranch w z + 2 * Real.pi * Complex.I := by
  rw [complexLogarithmBranch, Complex.exp_periodic]
  dsimp [complexLogarithmBranch]
  ring

@[simp] theorem complexLogarithmBranch_zero (z : ℂ) :
    complexLogarithmBranch 0 z = Complex.log z := by
  simp [complexLogarithmBranch]

theorem eventuallyEq_complexLogarithmBranch_log_ofReal {r : ℝ} (hr : 0 < r) :
    complexLogarithmBranch (Complex.log r) =ᶠ[𝓝 (r : ℂ)] Complex.log := by
  have hr₀ : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hs : (Complex.log (r : ℂ) - 0).im ∈ Ioo (-Real.pi) Real.pi := by
    rw [← Complex.ofReal_log hr.le]
    simpa using (show -Real.pi < (0 : ℝ) ∧ 0 < Real.pi by constructor <;> linarith [Real.pi_pos])
  have he := eventuallyEq_complexLogarithmBranch hs
  rw [Complex.exp_log hr₀] at he
  filter_upwards [he] with z hz
  simpa only [complexLogarithmBranch_zero] using hz

end DirichletL

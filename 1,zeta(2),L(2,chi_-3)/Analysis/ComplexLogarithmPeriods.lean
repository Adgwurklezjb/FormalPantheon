import Analysis.ComplexLogarithmCircle

/-!
Exact continuation periods for a derivative with a simple pole and an
analytic remainder. This supplies the local Wronskian periods for CDT v2,
Proposition `functionsH`, in the nonzero-branch step of `14functions`.
-/

namespace DirichletL

open Filter unitInterval
open scoped Topology

/-- A simple-pole derivative gives its exact logarithmic period on every small positive circle. -/
theorem exists_radius_analyticContinuationAlong_deriv_period {R : ℂ → ℂ}
    (hR : AnalyticAt ℂ R 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε → ∀ k : ℂ,
      ∀ F : I → ℂ → ℂ, AnalyticContinuationAlong (complexCirclePath r) F →
        (∀ t, ∀ᶠ z in 𝓝 (complexCirclePath r t), HasDerivAt (F t) (k / z + R z) z) →
        F 1 =ᶠ[𝓝 (r : ℂ)] fun z => F 0 z + k * (2 * Real.pi * Complex.I) := by
  obtain ⟨P, hPa, _, hPd⟩ := exists_analytic_primitive hR
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hPa.eventually_analyticAt.and hPd)
  refine ⟨ε, hε, ?_⟩
  intro r hr hrε k F hF hFd
  have hm (t : I) : complexCirclePath r t ∈ Metric.ball (0 : ℂ) ε := by
    simpa only [Metric.mem_ball, dist_zero_right, norm_complexCirclePath, abs_of_pos hr]
      using hrε
  let L : I → ℂ → ℂ := fun t z => P z + k * complexLogarithmBranch (complexCircleLift r t) z
  have hL : AnalyticContinuationAlong (complexCirclePath r) L := by
    have hP := AnalyticContinuationAlong.const (complexCirclePath r).continuous
      (fun t => (hball (hm t)).1)
    have hk : AnalyticContinuationAlong (complexCirclePath r) (fun _ _ => k) :=
      AnalyticContinuationAlong.const (complexCirclePath r).continuous (fun _ => analyticAt_const)
    have hl : AnalyticContinuationAlong (complexCirclePath r)
        (fun t => complexLogarithmBranch (complexCircleLift r t)) := by
      simpa only [exp_complexCircleLift hr] using
        analyticContinuationAlong_complexLogarithmBranch (continuous_complexCircleLift r)
    exact hP.add (hk.mul hl)
  have hLd (t : I) : ∀ᶠ z in 𝓝 (complexCirclePath r t),
      HasDerivAt (L t) (k / z + R z) z := by
    have hs : complexCirclePath r t / Complex.exp (complexCircleLift r t) ∈ Complex.slitPlane := by
      rw [← exp_complexCircleLift hr t]
      simp [Complex.exp_ne_zero]
    have hd := (continuous_id.div_const (Complex.exp (complexCircleLift r t))).continuousAt
      (x := complexCirclePath r t)
    have hn := hd.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds hs)
    filter_upwards [Metric.isOpen_ball.mem_nhds (hm t), hn] with z hz hzs
    simpa only [L, div_eq_mul_inv, add_comm] using
      (hball hz).2.add ((hasDerivAt_complexLogarithmBranch hzs).const_mul k)
  have hd : ∀ᶠ z in 𝓝 (complexCirclePath r 0),
      HasDerivAt (fun w => F 0 w - L 0 w) 0 z := by
    filter_upwards [hFd 0, hLd 0] with z hf hl
    simpa only [sub_self] using hf.sub hl
  have he := eventuallyEq_const_of_eventually_hasDerivAt_zero hd
  simp only [Path.source] at he
  let K := F 0 (r : ℂ) - L 0 (r : ℂ)
  have hi : F 0 =ᶠ[𝓝 (r : ℂ)] fun z => L 0 z + K := by
    filter_upwards [he] with z hz
    exact (sub_eq_iff_eq_add.mp hz).trans (add_comm _ _)
  have hK : AnalyticContinuationAlong (complexCirclePath r) (fun _ _ => K) :=
    AnalyticContinuationAlong.const (complexCirclePath r).continuous (fun _ => analyticAt_const)
  have h1 : F 1 =ᶠ[𝓝 (r : ℂ)] fun z => L 1 z + K := by
    simpa only [Path.target] using hF.eq_of_preconnectedSpace (hL.add hK)
      (t₀ := 0) (by simpa only [Path.source] using hi) 1
  filter_upwards [h1, hi] with z hz hi
  rw [hz, hi]
  dsimp [L]
  rw [complexCircleLift_one, complexCircleLift_zero, complexLogarithmBranch_add_period]
  ring

/-- A nonzero simple-pole coefficient forces unequal endpoint germs on small circles. -/
theorem exists_radius_analyticContinuationAlong_deriv_ne {R : ℂ → ℂ}
    (hR : AnalyticAt ℂ R 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε → ∀ k : ℂ, k ≠ 0 →
      ∀ F : I → ℂ → ℂ, AnalyticContinuationAlong (complexCirclePath r) F →
        (∀ t, ∀ᶠ z in 𝓝 (complexCirclePath r t), HasDerivAt (F t) (k / z + R z) z) →
        ¬F 1 =ᶠ[𝓝 (r : ℂ)] F 0 := by
  obtain ⟨ε, hε, hperiod⟩ := exists_radius_analyticContinuationAlong_deriv_period hR
  refine ⟨ε, hε, ?_⟩
  intro r hr hrε k hk F hF hFd he
  have hp := (hperiod r hr hrε k F hF hFd).eq_of_nhds
  have he' := he.eq_of_nhds
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hn := mul_ne_zero hk (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hpi)
    Complex.I_ne_zero)
  exact hn (by linear_combination he' - hp)

end DirichletL

import Analysis.AnalyticLinearODEHomotopyExtension

/-!
Continuation from an actual inner solution through a regular annulus.
Source: CDT v2 TeX 1739-1744 and 7157-7173. Prior meaning and radius checks:
-/

namespace DirichletL

open scoped Topology Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_analytic_matrix_extension_on_ball
    {I : Type*} [Fintype I] {M : ℂ → Matrix I I ℂ}
    {a r R : ℝ} (ha : 0 < a) (har : a < r) (hrR : r < R)
    (hM : AnalyticOnNhd ℂ M {z : ℂ | a < ‖z‖ ∧ ‖z‖ < R})
    {f : ℂ → I → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball 0 r))
    (hfo : ∀ z : ℂ, a < ‖z‖ → ‖z‖ < r → HasDerivAt f (M z *ᵥ f z) z) :
    ∃ g : ℂ → I → ℂ, AnalyticOnNhd ℂ g (Metric.ball 0 R) ∧
      Set.EqOn g f (Metric.ball 0 r) ∧
      ∀ z : ℂ, a < ‖z‖ → ‖z‖ < R → HasDerivAt g (M z *ᵥ g z) z := by
  let D : AnalyticMatrixODE I :=
    ⟨{z : ℂ | a < ‖z‖ ∧ ‖z‖ < R},
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const), M, hM⟩
  let s : ℝ := (a + r) / 2
  have has : a < s := by dsimp [s]; linarith
  have hsr : s < r := by dsimp [s]; linarith
  have hsR : s < R := hsr.trans hrR
  have hs : 0 < s := ha.trans has
  let b : D.domain := ⟨(s : ℂ), by
    change a < ‖(s : ℂ)‖ ∧ ‖(s : ℂ)‖ < R
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] using
      (show a < s ∧ s < R from ⟨has, hsR⟩)⟩
  let F (p : unitInterval × D.domain) : ℂ :=
    ((1 - (p.1 : ℝ)) * s / ‖(p.2 : ℂ)‖ + (p.1 : ℝ)) • (p.2 : ℂ)
  have hnorm (t : unitInterval) (z : D.domain) :
      ‖F (t, z)‖ = (1 - (t : ℝ)) * s + (t : ℝ) * ‖(z : ℂ)‖ := by
    have hz : 0 < ‖(z : ℂ)‖ := ha.trans z.property.1
    have hc : 0 ≤ (1 - (t : ℝ)) * s / ‖(z : ℂ)‖ + (t : ℝ) :=
      add_nonneg (div_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) hs.le) hz.le)
        t.property.1
    dsimp only [F]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    field_simp [ne_of_gt hz]
  have hFmem (p : unitInterval × D.domain) : F p ∈ D.domain := by
    change a < ‖F p‖ ∧ ‖F p‖ < R
    rw [hnorm]
    exact (convex_Ioo a R) ⟨has, hsR⟩ p.2.property
      (sub_nonneg.mpr p.1.property.2) p.1.property.1 (by ring)
  have hFc : Continuous F := by
    have ht : Continuous (fun p : unitInterval × D.domain => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hz : Continuous (fun p : unitInterval × D.domain => (p.2 : ℂ)) :=
      continuous_subtype_val.comp continuous_snd
    exact ((((continuous_const.sub ht).mul continuous_const).div hz.norm
      (fun p => ne_of_gt (ha.trans p.2.property.1))).add ht).smul hz
  let H : C(unitInterval × D.domain, D.domain) :=
    ⟨fun p => ⟨F p, hFmem p⟩, hFc.subtype_mk _⟩
  have hzero (z : D.domain) : (H (0, z) : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    change dist (F (0, z)) 0 < r
    rw [dist_zero_right, hnorm]
    simpa using hsr
  have hone (z : D.domain) : H (1, z) = z := by
    apply Subtype.ext
    simp [H, F]
  have hstay (t : unitInterval) (z : D.domain)
      (hz : (z : ℂ) ∈ Metric.ball (0 : ℂ) r) :
      (H (t, z) : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    have hz' : ‖(z : ℂ)‖ < r := by simpa using hz
    change dist (F (t, z)) 0 < r
    rw [dist_zero_right, hnorm]
    exact (convex_Iio r) hsr hz'
      (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
  obtain ⟨g, hga, hgeq, hgd⟩ := D.exists_analytic_extension_of_homotopy b
    Metric.isOpen_ball hf
    (fun z hz => hfo z hz.1.1 (by simpa using hz.2)) H hzero hone hstay
  refine ⟨g, ?_, hgeq, fun z hza hzR => hgd z ⟨hza, hzR⟩⟩
  intro z hz
  apply hga z
  by_cases hzr : ‖z‖ < r
  · exact Or.inl (by simpa using hzr)
  · exact Or.inr ⟨har.trans_le (le_of_not_gt hzr), by simpa using hz⟩

end DirichletL

import Mathlib

/-!
Local logarithmic bounds for CDT v2's radius limit, supplied TeX 4150-4153.
-/

open Filter
open scoped Topology

namespace DirichletL

theorem exists_local_analytic_log_factor_bound {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hne : ¬∀ᶠ z in 𝓝 a, f z = 0) :
    ∃ (n : ℕ) (δ C : ℝ), 0 < δ ∧ 0 ≤ C ∧
      ∀ z ∈ Metric.ball a δ, z ≠ a →
        |Real.log ‖f z‖| ≤ (n : ℝ) * |Real.log ‖z - a‖| + C := by
  obtain ⟨n, g, hg, hga, hfactor⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  let C : ℝ := |Real.log ‖g a‖| + 1
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hcont : ContinuousAt (fun z => |Real.log ‖g z‖|) a :=
    (hg.continuousAt.norm.log (norm_ne_zero_iff.mpr hga)).abs
  have hbound : ∀ᶠ z in 𝓝 a, |Real.log ‖g z‖| < C :=
    hcont.tendsto.eventually (eventually_lt_nhds (by dsimp only [C]; linarith))
  have hgood := hfactor.and ((hg.continuousAt.eventually_ne hga).and hbound)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨n, δ, C, hδ, hC, ?_⟩
  intro z hz hza
  obtain ⟨hfac, hgz, hgzbound⟩ := hball hz
  have hlog : Real.log ‖f z‖ =
      (n : ℝ) * Real.log ‖z - a‖ + Real.log ‖g z‖ := by
    rw [hfac, norm_smul, norm_pow,
      Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hza)))
        (norm_ne_zero_iff.mpr hgz), Real.log_pow]
  rw [hlog]
  calc
    _ ≤ |(n : ℝ) * Real.log ‖z - a‖| + |Real.log ‖g z‖| := abs_add_le _ _
    _ ≤ (n : ℝ) * |Real.log ‖z - a‖| + C := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
      exact add_le_add_left hgzbound.le _

end DirichletL

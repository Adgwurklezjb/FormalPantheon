import Analysis.LocalExpansions

/-!
Meromorphic differentiation and the scaled derivative of a pullback germ.
This supports the G derivatives in CDT v2 `14functions`, TeX 8044-8051.
-/

namespace DirichletL

open Filter
open scoped Topology

theorem meromorphicAt_deriv {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) :
    MeromorphicAt (deriv f) a := by
  obtain ⟨N, g, hg, he⟩ := MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mp hf
  have he' : f =ᶠ[𝓝[≠] a] fun z => (z - a) ^ N * g z := by
    simpa only [smul_eq_mul] using he
  obtain ⟨u, hu, _, hd⟩ := exists_analytic_factor_deriv N hg he'
  exact (((analyticAt_id.sub analyticAt_const).meromorphicAt.zpow' (N - 1)).mul'
    hu.meromorphicAt).congr hd.symm

theorem eventuallyEq_deriv_div_of_eventuallyEq_comp {F f φ : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f (φ a)) (hφ : AnalyticAt ℂ φ a) (hφd : deriv φ a ≠ 0)
    (he : F =ᶠ[𝓝 a] fun z => f (φ z)) :
    (fun z => deriv F z / deriv φ z) =ᶠ[𝓝 a] fun z => deriv f (φ z) := by
  filter_upwards [he.deriv, hφ.eventually_analyticAt,
    hφ.continuousAt.tendsto.eventually hf.eventually_analyticAt,
    hφ.deriv.continuousAt.eventually_ne hφd] with z hFeq hφz hfz hne
  have hd := hfz.differentiableAt.hasDerivAt.comp z hφz.differentiableAt.hasDerivAt
  simp only [Function.comp_def] at hd
  rw [hFeq, hd.deriv, mul_div_cancel_right₀ _ hne]

end DirichletL

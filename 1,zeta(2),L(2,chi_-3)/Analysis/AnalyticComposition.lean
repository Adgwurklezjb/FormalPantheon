import Mathlib

/-!
Local analytic change of variable for CDT v2 equations `y in x` and
`explicitode`. The fourth chain rule extends Mathlib's third chain rule.
-/

namespace DirichletL

open Filter
open scoped Topology

theorem deriv_four_comp_of_analyticAt {f g : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g (f x)) :
    deriv (deriv (deriv (deriv (g ∘ f)))) x =
      deriv (deriv (deriv (deriv g))) (f x) * deriv f x ^ 4 +
        6 * deriv (deriv (deriv g)) (f x) * deriv f x ^ 2 * deriv (deriv f) x +
        deriv (deriv g) (f x) * (3 * deriv (deriv f) x ^ 2 +
          4 * deriv f x * deriv (deriv (deriv f)) x) +
        deriv g (f x) * deriv (deriv (deriv (deriv f))) x := by
  have he : deriv (deriv (deriv (g ∘ f))) =ᶠ[𝓝 x] fun z =>
      deriv (deriv (deriv g)) (f z) * deriv f z ^ 3 +
        3 * deriv (deriv g) (f z) * deriv (deriv f) z * deriv f z +
        deriv g (f z) * deriv (deriv (deriv f)) z := by
    filter_upwards [hf.eventually_analyticAt,
      hf.continuousAt.tendsto.eventually hg.eventually_analyticAt] with z hfz hgz
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      iteratedDeriv_comp_three hgz.contDiffAt hfz.contDiffAt
  have hf₁ := hf.differentiableAt.hasDerivAt
  have hf₂ := hf.deriv.differentiableAt.hasDerivAt
  have hf₃ := hf.deriv.deriv.differentiableAt.hasDerivAt
  have hf₄ := hf.deriv.deriv.deriv.differentiableAt.hasDerivAt
  have hg₁ := hg.deriv.differentiableAt.hasDerivAt.comp x hf₁
  have hg₂ := hg.deriv.deriv.differentiableAt.hasDerivAt.comp x hf₁
  have hg₃ := hg.deriv.deriv.deriv.differentiableAt.hasDerivAt.comp x hf₁
  have h := ((hg₃.mul (hf₂.pow 3)).add
    ((((hg₂.const_mul 3).mul hf₃).mul hf₂))).add (hg₁.mul hf₄)
  simp only [Function.comp_def, Pi.mul_def, Pi.pow_def, Pi.add_def] at h
  rw [he.deriv_eq, h.deriv]
  ring

theorem exists_analyticAt_localInverse {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hne : deriv f x ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (f x) ∧ g (f x) = x ∧
      (g ∘ f) =ᶠ[𝓝 x] id ∧ (f ∘ g) =ᶠ[𝓝 (f x)] id := by
  have hd : HasStrictDerivAt f (deriv f x) x := hf.hasStrictFDerivAt.hasStrictDerivAt
  have hi := hd.hasStrictFDerivAt_equiv hne
  let e := hi.toPartialHomeomorph f
  have hx : x ∈ e.source := hi.mem_toPartialHomeomorph_source
  refine ⟨e.symm, ?_, e.left_inv hx, hi.eventually_left_inverse, hi.eventually_right_inverse⟩
  exact e.analyticAt_symm' hx hf hi.hasFDerivAt.fderiv

theorem eventuallyEq_of_comp_of_analyticAt {φ f g : ℂ → ℂ} {x : ℂ}
    (hφ : AnalyticAt ℂ φ x) (hne : deriv φ x ≠ 0)
    (he : (f ∘ φ) =ᶠ[𝓝 x] (g ∘ φ)) : f =ᶠ[𝓝 (φ x)] g := by
  rw [← hφ.hasStrictFDerivAt.hasStrictDerivAt.map_nhds_eq hne]
  exact eventuallyEq_map.mpr he

end DirichletL

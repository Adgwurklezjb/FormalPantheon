import Analysis.PairwiseMaximumL1

/-!
Symmetry for CDT v2's two-radius application, supplied TeX 8384-8404.
-/

open MeasureTheory Set

namespace DirichletL

theorem pairwiseMaxIntegral_comm {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1) :
    pairwiseMaxIntegral f g = pairwiseMaxIntegral g f := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  rw [pairwiseMaxIntegral_eq_integral_prod hf hg,
    pairwiseMaxIntegral_eq_integral_prod hg hf]
  simpa only [Prod.swap, max_comm] using
    (integral_prod_swap (μ := μ) (ν := μ) (fun z : ℝ × ℝ => max (f z.1) (g z.2))).symm

end DirichletL

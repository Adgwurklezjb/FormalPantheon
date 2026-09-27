import Comparator.Statement

/-!
Centered bounded-variable input to CDT v2's Hoeffding argument,
supplied TeX 3220-3245. The native exponential chord and cosh estimates
supply the canonical sub-Gaussian moment bound with parameter one.
-/

namespace DirichletL

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

theorem integrable_exp_mul_of_abs_le_one [IsFiniteMeasure μ]
    (hX : AEMeasurable X μ) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ 1) (t : ℝ) :
    Integrable (fun ω => exp (t * X ω)) μ := by
  apply (integrable_const (exp |t|)).mono' (hX.const_mul t).exp.aestronglyMeasurable
  filter_upwards [hbound] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  apply exp_le_exp.mpr
  calc
    t * X ω ≤ |t * X ω| := le_abs_self _
    _ = |t| * |X ω| := abs_mul _ _
    _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hω (abs_nonneg _)
    _ = |t| := mul_one _

theorem hasSubgaussianMGF_of_abs_le_one [IsProbabilityMeasure μ]
    (hX : AEMeasurable X μ) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ 1)
    (hmean : ∫ ω, X ω ∂μ = 0) : HasSubgaussianMGF X 1 μ := by
  have hXi : Integrable X μ :=
    (integrable_const (1 : ℝ)).mono' hX.aestronglyMeasurable (by
      simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨integrable_exp_mul_of_abs_le_one hX hbound, ?_⟩
  intro t
  have hlin : Integrable (fun ω => cosh t + X ω * sinh t) μ :=
    (integrable_const _).add (hXi.mul_const _)
  calc
    mgf X μ t ≤ ∫ ω, (cosh t + X ω * sinh t) ∂μ := by
      apply integral_mono_ae (integrable_exp_mul_of_abs_le_one hX hbound t) hlin
      filter_upwards [hbound] with ω hω
      simpa only [mul_comm t] using exp_mul_le_cosh_add_mul_sinh hω t
    _ = cosh t := by
      rw [integral_add (integrable_const _) (hXi.mul_const _), integral_mul_const, hmean]
      simp
    _ ≤ exp ((1 : ℝ≥0) * t ^ 2 / 2) := by
      simpa using cosh_le_exp_half_sq t

theorem hasSubgaussianMGF_neg {c : ℝ≥0} (hX : HasSubgaussianMGF X c μ) :
    HasSubgaussianMGF (-X) c μ where
  integrable_exp_mul t := by
    simpa only [Pi.neg_apply, mul_neg, neg_mul] using hX.integrable_exp_mul (-t)
  mgf_le t := by
    rw [mgf_neg]
    simpa only [neg_sq] using hX.mgf_le (-t)

end DirichletL

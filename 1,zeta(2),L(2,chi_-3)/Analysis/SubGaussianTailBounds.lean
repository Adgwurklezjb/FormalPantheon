import Analysis.BoundedMomentGeneratingFunctions

/-!
Two-sided exponential bounds for the centered variables in CDT v2,
supplied TeX 3220-3245. All independence and moment hypotheses remain
explicit; native sub-Gaussian finite sums and a union bound give the tails.
-/

namespace DirichletL

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem measure_abs_ge_le_of_hasSubgaussianMGF {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) {r : ℝ} (hr : 0 ≤ r) :
    μ.real {ω | r ≤ |X ω|} ≤ 2 * exp (-r ^ 2 / (2 * c)) := by
  have heq : {ω | r ≤ |X ω|} = {ω | r ≤ X ω} ∪ {ω | r ≤ (-X) ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Pi.neg_apply, le_abs]
  rw [heq]
  calc
    _ ≤ μ.real {ω | r ≤ X ω} + μ.real {ω | r ≤ (-X) ω} := measureReal_union_le _ _
    _ ≤ exp (-r ^ 2 / (2 * c)) + exp (-r ^ 2 / (2 * c)) :=
      add_le_add (hX.measure_ge_le hr) ((hasSubgaussianMGF_neg hX).measure_ge_le hr)
    _ = _ := by ring

theorem measure_abs_sum_ge_le_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ}
    (hindep : iIndepFun X μ) {c : ι → ℝ≥0} {s : Finset ι}
    (hsub : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) {r : ℝ} (hr : 0 ≤ r) :
    μ.real {ω | r ≤ |∑ i ∈ s, X i ω|} ≤
      2 * exp (-r ^ 2 / (2 * ∑ i ∈ s, c i)) :=
  measure_abs_ge_le_of_hasSubgaussianMGF
    (HasSubgaussianMGF.sum_of_iIndepFun hindep hsub) hr

theorem measure_abs_sum_ge_le_of_bounded_centered [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} (hindep : iIndepFun X μ) {s : Finset ι}
    (hmeas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ 1)
    (hmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) {r : ℝ} (hr : 0 ≤ r) :
    μ.real {ω | r ≤ |∑ i ∈ s, X i ω|} ≤ 2 * exp (-r ^ 2 / (2 * (s.card : ℝ))) := by
  have hs : ∀ i ∈ s, HasSubgaussianMGF (X i) 1 μ :=
    fun i hi => hasSubgaussianMGF_of_abs_le_one (hmeas i hi) (hbound i hi) (hmean i hi)
  simpa using measure_abs_sum_ge_le_of_iIndepFun hindep hs hr

theorem measure_abs_sum_ge_mul_card_le_of_bounded_centered [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} (hindep : iIndepFun X μ) {s : Finset ι}
    (hmeas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ 1)
    (hmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) (hs : 0 < s.card)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε * s.card ≤ |∑ i ∈ s, X i ω|} ≤
      2 * exp (-ε ^ 2 * s.card / 2) := by
  have hn : 0 < (s.card : ℝ) := by exact_mod_cast hs
  have h := measure_abs_sum_ge_le_of_bounded_centered hindep hmeas hbound hmean
    (mul_nonneg hε hn.le)
  have heq : -(ε * (s.card : ℝ)) ^ 2 / (2 * s.card) = -ε ^ 2 * s.card / 2 := by
    field_simp [hn.ne']
  simpa only [heq] using h

end DirichletL

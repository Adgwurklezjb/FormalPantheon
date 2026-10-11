import Analysis.SubGaussianTailBounds

/-!
Centered indicator counts for the finite-grid concentration argument
used in place of CDT v2, supplied TeX 3220-3245 and 3950-4004.
All probabilities and finite cardinalities use their canonical definitions.
-/

namespace DirichletL

open MeasureTheory ProbabilityTheory Set Real
open scoped Classical

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem abs_indicator_sub_measureReal_le_one (s : Set Ω) (ω : Ω) :
    |s.indicator (fun _ => (1 : ℝ)) ω - μ.real s| ≤ 1 := by
  have hp0 : 0 ≤ μ.real s := measureReal_nonneg
  have hp1 : μ.real s ≤ 1 := measureReal_le_one
  by_cases hω : ω ∈ s
  · rw [Set.indicator_of_mem hω]
    apply abs_le.mpr
    constructor <;> linarith
  · simp only [Set.indicator_of_not_mem hω, zero_sub, abs_neg, abs_of_nonneg hp0]
    exact hp1

theorem integral_indicator_sub_measureReal {s : Set Ω} (hs : MeasurableSet s) :
    (∫ ω, s.indicator (fun _ => (1 : ℝ)) ω - μ.real s ∂μ) = 0 := by
  rw [integral_sub ((integrable_const (1 : ℝ)).indicator hs) (integrable_const _)]
  simp [hs]

theorem measure_abs_indicator_average_sub_mean_le {d : ℕ} (hd : 0 < d)
    {X : Fin d → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    {A : Fin d → Set ℝ} (hA : ∀ i, MeasurableSet (A i)) {r : ℝ} (hr : 0 ≤ r) :
    μ.real {ω | r ≤ |((Finset.univ.filter fun i : Fin d => X i ω ∈ A i).card : ℝ) / d -
      (∑ i : Fin d, μ.real (X i ⁻¹' A i)) / d|} ≤ 2 * exp (-r ^ 2 * d / 2) := by
  classical
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  let p : Fin d → ℝ := fun i => μ.real (X i ⁻¹' A i)
  let Y : Fin d → Ω → ℝ := fun i ω => (A i).indicator (fun _ => (1 : ℝ)) (X i ω) - p i
  have hYmeas : ∀ i, Measurable (Y i) := fun i =>
    ((measurable_const.indicator (hA i)).comp (hX i)).sub_const (p i)
  have hYind := hindep.comp
    (fun i x => (A i).indicator (fun _ => (1 : ℝ)) x - p i)
    (fun i => (measurable_const.indicator (hA i)).sub_const (p i))
  change iIndepFun Y μ at hYind
  have hYi (i : Fin d) : Y i = fun ω =>
      (X i ⁻¹' A i).indicator (fun _ => (1 : ℝ)) ω - μ.real (X i ⁻¹' A i) := by
    funext ω
    by_cases h : X i ω ∈ A i <;> simp [Y, p, h]
  have hYbound : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ 1 := by
    intro i
    rw [hYi i]
    exact Filter.Eventually.of_forall (abs_indicator_sub_measureReal_le_one _)
  have hYmean : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    rw [hYi i]
    exact integral_indicator_sub_measureReal ((hA i).preimage (hX i))
  have htail := measure_abs_sum_ge_mul_card_le_of_bounded_centered
    (s := Finset.univ) hYind (fun i _ => (hYmeas i).aemeasurable)
    (fun i _ => hYbound i) (fun i _ => hYmean i) (by simpa using hd) hr
  have hsum (ω : Ω) : (∑ i : Fin d, Y i ω) =
      ((Finset.univ.filter fun i : Fin d => X i ω ∈ A i).card : ℝ) - ∑ i : Fin d, p i := by
    simp only [Y, Finset.sum_sub_distrib]
    congr 1
    simp only [Set.indicator_apply, Finset.sum_boole]
  have hevent : {ω | r ≤
      |((Finset.univ.filter fun i : Fin d => X i ω ∈ A i).card : ℝ) / d -
        (∑ i : Fin d, μ.real (X i ⁻¹' A i)) / d|} =
      {ω | r * d ≤ |∑ i : Fin d, Y i ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq, hsum, p, ← sub_div, abs_div, abs_of_pos hdR,
      le_div_iff₀ hdR]
  rw [hevent]
  simpa only [Finset.card_univ, Fintype.card_fin] using htail

theorem measure_abs_indicator_average_sub_center_le {d : ℕ} (hd : 0 < d)
    {X : Fin d → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    {A : Fin d → Set ℝ} (hA : ∀ i, MeasurableSet (A i)) {r β u : ℝ} (hr : 0 ≤ r)
    (hbias : ∀ i, |μ.real (X i ⁻¹' A i) - u| ≤ β) :
    μ.real {ω | r + β ≤
      |((Finset.univ.filter fun i : Fin d => X i ω ∈ A i).card : ℝ) / d - u|} ≤
      2 * exp (-r ^ 2 * d / 2) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  let p : Fin d → ℝ := fun i => μ.real (X i ⁻¹' A i)
  have hsum : |∑ i : Fin d, (p i - u)| ≤ (d : ℝ) * β := by
    calc
      _ ≤ ∑ i : Fin d, |p i - u| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, β := Finset.sum_le_sum (fun i _ => hbias i)
      _ = _ := by simp
  have heq : (∑ i : Fin d, p i) / (d : ℝ) - u =
      (∑ i : Fin d, (p i - u)) / (d : ℝ) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hdR.ne']
  have hmean : |(∑ i : Fin d, p i) / (d : ℝ) - u| ≤ β := by
    rw [heq, abs_div, abs_of_pos hdR]
    exact (div_le_iff₀ hdR).mpr (by simpa only [mul_comm] using hsum)
  have htail := measure_abs_indicator_average_sub_mean_le hd hX hindep hA hr
  apply le_trans (measureReal_mono ?_) htail
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have htri := abs_sub_le
    (((Finset.univ.filter fun i : Fin d => X i ω ∈ A i).card : ℝ) / d)
    ((∑ i : Fin d, p i) / d) u
  change r ≤ |((Finset.univ.filter fun i : Fin d => X i ω ∈ A i).card : ℝ) / d -
    (∑ i : Fin d, p i) / d|
  linarith

end DirichletL

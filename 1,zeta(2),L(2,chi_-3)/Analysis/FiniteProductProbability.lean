import Comparator.Statement

/-!
Exact finite product probabilities for the auxiliary parameter count
in CDT v2, supplied TeX 3950-4004. The canonical product measure and
uniform finite PMF retain both independence and integer cardinalities.
-/

namespace DirichletL

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal Classical

section Product

variable {ι : Type*} [Fintype ι] {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
  [∀ i, IsProbabilityMeasure (μ i)]

theorem map_pi_eval (i : ι) : (Measure.pi μ).map (eval i) = μ i := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs, ← univ_pi_update_univ i s,
    Measure.pi_pi]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

theorem iIndepFun_pi_eval : iIndepFun (fun i : ι => eval i) (Measure.pi μ) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_pi_apply i).aemeasurable)).mpr
  change (Measure.pi μ).map id = Measure.pi (fun i => (Measure.pi μ).map (eval i))
  rw [Measure.map_id]
  congr 1
  funext i
  exact (map_pi_eval μ i).symm

end Product

theorem uniformOfFintype_real_finset {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (s : Finset α) :
    (PMF.uniformOfFintype α).toMeasure.real (s : Set α) =
      (s.card : ℝ) / Fintype.card α := by
  rw [Measure.real, PMF.toMeasure_uniformOfFintype_apply (s : Set α) s.measurableSet]
  have hc : Fintype.card (s : Set α) = s.card := Fintype.card_coe s
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, hc]

theorem pi_uniformOfFintype_toMeasure {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)] :
    Measure.pi (fun i => (PMF.uniformOfFintype (α i)).toMeasure) =
      (PMF.uniformOfFintype (∀ i, α i)).toMeasure := by
  classical
  apply Measure.ext_of_singleton
  intro x
  calc
    _ = ∏ i, (PMF.uniformOfFintype (α i)).toMeasure {x i} := by
      rw [← Set.univ_pi_singleton x, Measure.pi_pi]
    _ = ∏ i, (Fintype.card (α i) : ℝ≥0∞)⁻¹ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
        PMF.uniformOfFintype_apply]
    _ = ((∏ i, Fintype.card (α i) : ℕ) : ℝ≥0∞)⁻¹ := by
      rw [Nat.cast_prod]
      exact (ENNReal.prod_inv_distrib (by
        intro _ _ _ _ _
        exact Or.inr (ENNReal.natCast_ne_top _))).symm
    _ = _ := by
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
        PMF.uniformOfFintype_apply, Fintype.card_pi]

theorem pi_uniformOfFintype_real_finset {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
    (s : Finset (∀ i, α i)) :
    (Measure.pi (fun i => (PMF.uniformOfFintype (α i)).toMeasure)).real (s : Set (∀ i, α i)) =
      (s.card : ℝ) / (∏ i, Fintype.card (α i) : ℕ) := by
  rw [pi_uniformOfFintype_toMeasure, uniformOfFintype_real_finset, Fintype.card_pi]

end DirichletL

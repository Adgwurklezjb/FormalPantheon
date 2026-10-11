import Analysis.DiscrepancyConcentration
import Analysis.FiniteProductProbability

/-!
Exact uniform finite counts for the auxiliary parameters in CDT v2,
supplied TeX 3950-4004. The finite-grid population biases remain explicit.
-/

namespace DirichletL

open MeasureTheory ProbabilityTheory Set Real
open scoped Classical

theorem real_pi_uniform_eval_preimage {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (i : ι) (s : Finset α) :
    (Measure.pi (fun _ : ι => (PMF.uniformOfFintype α).toMeasure)).real
      {t : ι → α | t i ∈ s} = (s.card : ℝ) / Fintype.card α := by
  have heval : Measurable (fun t : ι → α => t i) := measurable_pi_apply i
  have hm := congrArg (fun ν : Measure α => ν.real (s : Set α))
    (map_pi_eval (fun _ : ι => (PMF.uniformOfFintype α).toMeasure) i)
  simpa only [Measure.real, Measure.map_apply heval s.measurableSet] using
    hm.trans (uniformOfFintype_real_finset s)

theorem card_bad_discrepancy_div_le_of_grid_bias {α : Type*} [Fintype α] [Nonempty α]
    {d q : ℕ} (hd : 0 < d) (hq : 0 < q) (f : α → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hmesh : 1 / (q : ℝ) ≤ ε / 8)
    (hLE : ∀ k : Fin (q + 1),
      |((Finset.univ.filter fun a : α => f a ≤ (k.val : ℝ) / q).card : ℝ) / Fintype.card α -
        (k.val : ℝ) / q| ≤ ε / 8)
    (hLT : ∀ k : Fin (q + 1),
      |((Finset.univ.filter fun a : α => f a < (k.val : ℝ) / q).card : ℝ) / Fintype.card α -
        (k.val : ℝ) / q| ≤ ε / 8) :
    ((Finset.univ.filter fun t : Fin d → α => ¬HasIntervalDiscrepancyLE (f ∘ t) ε).card : ℝ) /
      (Fintype.card α : ℝ) ^ d ≤ 4 * (q + 1 : ℕ) * exp (-ε ^ 2 * d / 128) := by
  letI : MeasurableSpace α := ⊤
  let μ : Measure (Fin d → α) :=
    Measure.pi (fun _ : Fin d => (PMF.uniformOfFintype α).toMeasure)
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let X : Fin d → (Fin d → α) → ℝ := fun i t => f (t i)
  have hX : ∀ i, Measurable (X i) :=
    fun i => (measurable_of_countable f).comp (measurable_pi_apply i)
  have hindep := (iIndepFun_pi_eval
    (fun _ : Fin d => (PMF.uniformOfFintype α).toMeasure)).comp
    (fun _ => f) (fun _ => measurable_of_countable f)
  change iIndepFun X μ at hindep
  have hm (i : Fin d) (P : ℝ → Prop) : μ.real {t | P (X i t)} =
      ((Finset.univ.filter fun a : α => P (f a)).card : ℝ) / Fintype.card α := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      real_pi_uniform_eval_preimage i (Finset.univ.filter fun a : α => P (f a))
  have hLE' (k : Fin (q + 1)) (i : Fin d) :
      |μ.real {t | X i t ≤ (k.val : ℝ) / q} - (k.val : ℝ) / q| ≤ ε / 8 := by
    rw [hm i (fun x => x ≤ (k.val : ℝ) / q)]
    exact hLE k
  have hLT' (k : Fin (q + 1)) (i : Fin d) :
      |μ.real {t | X i t < (k.val : ℝ) / q} - (k.val : ℝ) / q| ≤ ε / 8 := by
    rw [hm i (fun x => x < (k.val : ℝ) / q)]
    exact hLT k
  have hconc := measure_not_hasIntervalDiscrepancyLE_le_of_grid_bias
    hd hq hX hindep hε hmesh hLE' hLT'
  let bad := Finset.univ.filter fun t : Fin d → α => ¬HasIntervalDiscrepancyLE (f ∘ t) ε
  have hset : (bad : Set (Fin d → α)) = {t | ¬HasIntervalDiscrepancyLE (f ∘ t) ε} := by
    ext t
    simp [bad]
  have hcard := pi_uniformOfFintype_real_finset (α := fun _ : Fin d => α) bad
  rw [hset] at hcard
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow] at hcard
  change μ.real {t | ¬HasIntervalDiscrepancyLE (f ∘ t) ε} ≤ _ at hconc
  rw [hcard] at hconc
  exact hconc

theorem one_sub_le_card_good_discrepancy_div_of_grid_bias
    {α : Type*} [Fintype α] [Nonempty α] {d q : ℕ} (hd : 0 < d) (hq : 0 < q)
    (f : α → ℝ) {ε : ℝ} (hε : 0 < ε) (hmesh : 1 / (q : ℝ) ≤ ε / 8)
    (hLE : ∀ k : Fin (q + 1),
      |((Finset.univ.filter fun a : α => f a ≤ (k.val : ℝ) / q).card : ℝ) / Fintype.card α -
        (k.val : ℝ) / q| ≤ ε / 8)
    (hLT : ∀ k : Fin (q + 1),
      |((Finset.univ.filter fun a : α => f a < (k.val : ℝ) / q).card : ℝ) / Fintype.card α -
        (k.val : ℝ) / q| ≤ ε / 8) :
    1 - 4 * (q + 1 : ℕ) * exp (-ε ^ 2 * d / 128) ≤
      ((Finset.univ.filter fun t : Fin d → α => HasIntervalDiscrepancyLE (f ∘ t) ε).card : ℝ) /
        (Fintype.card α : ℝ) ^ d := by
  have hbad := card_bad_discrepancy_div_le_of_grid_bias hd hq f hε hmesh hLE hLT
  let good := Finset.univ.filter fun t : Fin d → α => HasIntervalDiscrepancyLE (f ∘ t) ε
  let bad := Finset.univ.filter fun t : Fin d → α => ¬HasIntervalDiscrepancyLE (f ∘ t) ε
  have hn : 0 < (Fintype.card α : ℝ) ^ d :=
    pow_pos (by exact_mod_cast Fintype.card_pos) d
  have hc : good.card + bad.card = (Fintype.card α) ^ d := by
    simpa only [good, bad, Finset.card_univ, Fintype.card_fun, Fintype.card_fin] using
      (Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.univ)
        (fun t : Fin d → α => HasIntervalDiscrepancyLE (f ∘ t) ε))
  have hcR : (good.card : ℝ) + (bad.card : ℝ) = (Fintype.card α : ℝ) ^ d := by
    exact_mod_cast hc
  have htotal : (good.card : ℝ) / (Fintype.card α : ℝ) ^ d +
      (bad.card : ℝ) / (Fintype.card α : ℝ) ^ d = 1 := by
    rw [← add_div, hcR, div_self hn.ne']
  change (bad.card : ℝ) / (Fintype.card α : ℝ) ^ d ≤ _ at hbad
  change _ ≤ (good.card : ℝ) / (Fintype.card α : ℝ) ^ d
  linarith

end DirichletL

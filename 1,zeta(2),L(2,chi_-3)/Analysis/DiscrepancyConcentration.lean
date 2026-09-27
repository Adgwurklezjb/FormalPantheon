import Analysis.DiscrepancyGrid
import Analysis.IndicatorConcentration

/-!
Finite-grid concentration sufficient for the auxiliary count in CDT v2,
supplied TeX 3950-4004. The independently checked replacement of the
-/

namespace DirichletL

open MeasureTheory ProbabilityTheory Set Real

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem measure_not_hasIntervalDiscrepancyLE_le {d q : ℕ} (hd : 0 < d) (hq : 0 < q)
    {X : Fin d → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    {r β : ℝ} (hr : 0 ≤ r)
    (hLE : ∀ k : Fin (q + 1), ∀ i : Fin d,
      |μ.real {ω | X i ω ≤ (k.val : ℝ) / q} - (k.val : ℝ) / q| ≤ β)
    (hLT : ∀ k : Fin (q + 1), ∀ i : Fin d,
      |μ.real {ω | X i ω < (k.val : ℝ) / q} - (k.val : ℝ) / q| ≤ β) :
    μ.real {ω | ¬HasIntervalDiscrepancyLE (fun i => X i ω) (2 * (r + β + 1 / q))} ≤
      4 * (q + 1 : ℕ) * exp (-r ^ 2 * d / 2) := by
  let L : Fin (q + 1) → Set Ω := fun k => {ω | r + β ≤
    |((Finset.univ.filter fun i : Fin d => X i ω ≤ (k.val : ℝ) / q).card : ℝ) / d -
      (k.val : ℝ) / q|}
  let U : Fin (q + 1) → Set Ω := fun k => {ω | r + β ≤
    |((Finset.univ.filter fun i : Fin d => X i ω < (k.val : ℝ) / q).card : ℝ) / d -
      (k.val : ℝ) / q|}
  have hL (k : Fin (q + 1)) : μ.real (L k) ≤ 2 * exp (-r ^ 2 * d / 2) := by
    exact measure_abs_indicator_average_sub_center_le hd hX hindep
      (A := fun _ => Iic ((k.val : ℝ) / q)) (fun _ => measurableSet_Iic) hr (hLE k)
  have hU (k : Fin (q + 1)) : μ.real (U k) ≤ 2 * exp (-r ^ 2 * d / 2) := by
    exact measure_abs_indicator_average_sub_center_le hd hX hindep
      (A := fun _ => Iio ((k.val : ℝ) / q)) (fun _ => measurableSet_Iio) hr (hLT k)
  have hsub : {ω | ¬HasIntervalDiscrepancyLE (fun i => X i ω)
      (2 * (r + β + 1 / q))} ⊆ ⋃ k, L k ∪ U k := by
    intro ω hω
    by_contra hn
    have hgoodLE : ∀ k : Fin (q + 1),
        |((Finset.univ.filter fun i : Fin d => X i ω ≤ (k.val : ℝ) / q).card : ℝ) / d -
          (k.val : ℝ) / q| ≤ r + β := by
      intro k
      have hnot : ω ∉ L k := fun hk => hn (mem_iUnion.mpr ⟨k, Or.inl hk⟩)
      exact le_of_lt (lt_of_not_ge hnot)
    have hgoodLT : ∀ k : Fin (q + 1),
        |((Finset.univ.filter fun i : Fin d => X i ω < (k.val : ℝ) / q).card : ℝ) / d -
          (k.val : ℝ) / q| ≤ r + β := by
      intro k
      have hnot : ω ∉ U k := fun hk => hn (mem_iUnion.mpr ⟨k, Or.inr hk⟩)
      exact le_of_lt (lt_of_not_ge hnot)
    exact hω (hasIntervalDiscrepancyLE_of_grid hq hgoodLE hgoodLT)
  calc
    _ ≤ μ.real (⋃ k, L k ∪ U k) := measureReal_mono hsub
    _ ≤ ∑ k, μ.real (L k ∪ U k) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : Fin (q + 1),
        (2 * exp (-r ^ 2 * d / 2) + 2 * exp (-r ^ 2 * d / 2)) := by
      apply Finset.sum_le_sum
      intro k _
      exact (measureReal_union_le _ _).trans (add_le_add (hL k) (hU k))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem measure_not_hasIntervalDiscrepancyLE_le_of_grid_bias {d q : ℕ}
    (hd : 0 < d) (hq : 0 < q) {X : Fin d → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    {ε : ℝ} (hε : 0 < ε) (hmesh : 1 / (q : ℝ) ≤ ε / 8)
    (hLE : ∀ k : Fin (q + 1), ∀ i : Fin d,
      |μ.real {ω | X i ω ≤ (k.val : ℝ) / q} - (k.val : ℝ) / q| ≤ ε / 8)
    (hLT : ∀ k : Fin (q + 1), ∀ i : Fin d,
      |μ.real {ω | X i ω < (k.val : ℝ) / q} - (k.val : ℝ) / q| ≤ ε / 8) :
    μ.real {ω | ¬HasIntervalDiscrepancyLE (fun i => X i ω) ε} ≤
      4 * (q + 1 : ℕ) * exp (-ε ^ 2 * d / 128) := by
  have herr : 2 * (ε / 8 + ε / 8 + 1 / (q : ℝ)) ≤ ε := by linarith
  have hsub : {ω | ¬HasIntervalDiscrepancyLE (fun i => X i ω) ε} ⊆
      {ω | ¬HasIntervalDiscrepancyLE (fun i => X i ω)
        (2 * (ε / 8 + ε / 8 + 1 / (q : ℝ)))} :=
    fun _ hω hsmall => hω (hsmall.mono herr)
  have h := (measureReal_mono hsub).trans
    (measure_not_hasIntervalDiscrepancyLE_le hd hq hX hindep (by positivity : 0 ≤ ε / 8) hLE hLT)
  have hexp : -(ε / 8) ^ 2 * (d : ℝ) / 2 = -ε ^ 2 * d / 128 := by ring
  simpa only [hexp] using h

end DirichletL

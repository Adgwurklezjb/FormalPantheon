import Analysis.FiniteFourierApproximation
import Analysis.DiscrepancyGrid

/-!
The finite Fourier witness for CDT v2, supplied TeX 4054-4067, and
published UDC Lemma 2.5.9. The finite grid, endpoint conventions, and
dimension-independent choices are checked before these proofs in
-/

namespace DirichletL

open MeasureTheory
open scoped Classical

attribute [local instance] fact_one_pos

theorem prefix_count_bounds_of_continuous_bounds {d : ℕ} (hd : 0 < d)
    (t : Fin d → ℝ) {u η : ℝ} (f g : C(AddCircle (1 : ℝ), ℝ))
    (hpoint : ∀ i, f (t i : AddCircle (1 : ℝ)) ≤ (if t i < u then 1 else 0) ∧
      (if t i ≤ u then 1 else 0) ≤ g (t i : AddCircle (1 : ℝ)))
    (hfint : u - η ≤ ∫ x, f x ∂AddCircle.haarAddCircle)
    (hgint : (∫ x, g x ∂AddCircle.haarAddCircle) ≤ u + η)
    (hfmean : |(∑ i, f (t i : AddCircle (1 : ℝ))) / (d : ℝ) -
      ∫ x, f x ∂AddCircle.haarAddCircle| ≤ η)
    (hgmean : |(∑ i, g (t i : AddCircle (1 : ℝ))) / (d : ℝ) -
      ∫ x, g x ∂AddCircle.haarAddCircle| ≤ η) :
    |((Finset.univ.filter fun i => t i ≤ u).card : ℝ) / d - u| ≤ 2 * η ∧
      |((Finset.univ.filter fun i => t i < u).card : ℝ) / d - u| ≤ 2 * η := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hlo := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hpoint i).1)
  have hhi := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hpoint i).2)
  simp only [Finset.sum_boole] at hlo hhi
  have hlo' := div_le_div_of_nonneg_right hlo hdR.le
  have hhi' := div_le_div_of_nonneg_right hhi hdR.le
  have hcard : (Finset.univ.filter fun i => t i < u).card ≤
      (Finset.univ.filter fun i => t i ≤ u).card := by
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.le
  have hcounts := div_le_div_of_nonneg_right (Nat.cast_le.mpr hcard :
    ((Finset.univ.filter fun i => t i < u).card : ℝ) ≤
      (Finset.univ.filter fun i => t i ≤ u).card) hdR.le
  obtain ⟨hflo, _⟩ := abs_le.mp hfmean
  obtain ⟨_, hghi⟩ := abs_le.mp hgmean
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

theorem exists_fourier_control_interval_discrepancy {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∃ a : ℝ, 0 < a ∧
      ∀ d : ℕ, 0 < d → ∀ t : Fin d → ℝ,
        (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) →
        (∀ m : ℕ, 0 < m → m ≤ K →
          ‖∑ i, fourier 1 (t i : AddCircle (1 : ℝ)) ^ m‖ ≤ a * (d : ℝ)) →
        HasIntervalDiscrepancyLE t ε := by
  obtain ⟨q, hq⟩ := exists_nat_gt (4 / ε)
  have hqR : (0 : ℝ) < q := (div_pos (by norm_num : (0 : ℝ) < 4) hε).trans hq
  have hqN : 0 < q := Nat.cast_pos.mp hqR
  have hmesh : (1 : ℝ) / q ≤ ε / 4 := by
    apply (div_le_iff₀ hqR).mpr
    have h := (div_lt_iff₀ hε).mp hq
    nlinarith only [h]
  let u (k : Fin (q + 1)) : ℝ := (k.val : ℝ) / q
  have hu (k : Fin (q + 1)) : u k ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hqR.le, ?_⟩
    exact (div_le_one hqR).mpr (Nat.cast_le.mpr (Nat.le_of_lt_succ k.isLt))
  choose f g hr hp hfi hgi using fun k : Fin (q + 1) =>
    exists_continuous_unitCircle_prefix_bounds (hu k) (by positivity : 0 < ε / 8)
  let family (s : Fin (q + 1) × Bool) : C(AddCircle (1 : ℝ), ℝ) :=
    if s.2 then g s.1 else f s.1
  obtain ⟨K, hK, a, ha, hfamily⟩ :=
    exists_fourier_control_finite_family family (by positivity : 0 < ε / 8)
  refine ⟨K, hK, a, ha, ?_⟩
  intro d hd t hcube hmode
  have hmean := hfamily d hd (fun i => (t i : AddCircle (1 : ℝ))) hmode
  have hcounts (k : Fin (q + 1)) := prefix_count_bounds_of_continuous_bounds hd t
    (f k) (g k) (fun i => hp k (t i) (hcube i)) (hfi k) (hgi k)
    (by simpa only [family, Bool.false_eq_true, ↓reduceIte] using hmean (k, false))
    (by simpa only [family, ↓reduceIte] using hmean (k, true))
  exact (hasIntervalDiscrepancyLE_of_grid hqN (fun k => (hcounts k).1)
    (fun k => (hcounts k).2)).mono (by linarith only [hmesh])

theorem exists_bounded_fourier_mode_of_not_hasIntervalDiscrepancyLE {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∃ a : ℝ, 0 < a ∧
      ∀ d : ℕ, 0 < d → ∀ t : Fin d → ℝ,
        (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) → ¬HasIntervalDiscrepancyLE t ε →
        ∃ m : ℕ, 0 < m ∧ m ≤ K ∧
          a * (d : ℝ) < ‖∑ i, fourier 1 (t i : AddCircle (1 : ℝ)) ^ m‖ := by
  obtain ⟨K, hK, a, ha, hcontrol⟩ := exists_fourier_control_interval_discrepancy hε
  refine ⟨K, hK, a, ha, ?_⟩
  intro d hd t hcube hbad
  by_contra! hmode
  exact hbad (hcontrol d hd t hcube hmode)

end DirichletL

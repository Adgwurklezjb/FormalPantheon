import Analysis.IntervalDiscrepancy

/-!
The deterministic finite-grid replacement for the concentration input in
CDT v2, supplied TeX 3197-3269 and 3950-4004. The independent comparison
-/

namespace DirichletL

theorem abs_sub_le_of_monotone_grid {q : ℕ} (hq : 0 < q) {F : ℝ → ℝ}
    (hmono : Monotone F) {η : ℝ}
    (hgrid : ∀ k : Fin (q + 1), |F ((k.val : ℝ) / q) - (k.val : ℝ) / q| ≤ η)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) : |F u - u| ≤ η + 1 / q := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  by_cases hu1 : u = 1
  · subst u
    have hg := hgrid ⟨q, Nat.lt_succ_self q⟩
    simp only [Fin.val_mk, div_self hqR.ne'] at hg
    exact hg.trans (le_add_of_nonneg_right (div_nonneg zero_le_one hqR.le))
  have hu' : u < 1 := (lt_or_eq_of_le hu.2).resolve_right hu1
  let k : ℕ := ⌊u * q⌋₊
  have hx : 0 ≤ u * q := mul_nonneg hu.1 hqR.le
  have hk : k < q := (Nat.floor_lt hx).mpr (by nlinarith)
  have hlo : (k : ℝ) / q ≤ u := (div_le_iff₀ hqR).mpr (Nat.floor_le hx)
  have hhi : u ≤ ((k : ℝ) + 1) / q :=
    (le_div_iff₀ hqR).mpr (Nat.lt_floor_add_one (u * q)).le
  have hgl := abs_le.mp (hgrid ⟨k, by omega⟩)
  have hgr := abs_le.mp (hgrid ⟨k + 1, by omega⟩)
  simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one] at hgl hgr
  have hwidth : ((k : ℝ) + 1) / q - (k : ℝ) / q = 1 / q := by ring
  apply abs_le.mpr
  constructor <;> linarith [hmono hlo, hmono hhi]

theorem monotone_count_le_div {d : ℕ} (t : Fin d → ℝ) :
    Monotone (fun u : ℝ => ((Finset.univ.filter fun i : Fin d => t i ≤ u).card : ℝ) / d) := by
  classical
  intro a b hab
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
  have hc : (Finset.univ.filter fun i : Fin d => t i ≤ a).card ≤
      (Finset.univ.filter fun i : Fin d => t i ≤ b).card := by
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.trans hab
  exact_mod_cast hc

theorem monotone_count_lt_div {d : ℕ} (t : Fin d → ℝ) :
    Monotone (fun u : ℝ => ((Finset.univ.filter fun i : Fin d => t i < u).card : ℝ) / d) := by
  classical
  intro a b hab
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
  have hc : (Finset.univ.filter fun i : Fin d => t i < a).card ≤
      (Finset.univ.filter fun i : Fin d => t i < b).card := by
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.trans_le hab
  exact_mod_cast hc

theorem card_closed_interval_eq_count_sub {d : ℕ} (t : Fin d → ℝ)
    {a b : ℝ} (hab : a ≤ b) :
    ((Finset.univ.filter fun i : Fin d => a ≤ t i ∧ t i ≤ b).card : ℝ) =
      ((Finset.univ.filter fun i : Fin d => t i ≤ b).card : ℝ) -
      ((Finset.univ.filter fun i : Fin d => t i < a).card : ℝ) := by
  classical
  let A := Finset.univ.filter fun i : Fin d => t i < a
  let B := Finset.univ.filter fun i : Fin d => t i ≤ b
  have hsub : A ⊆ B := by
    intro i hi
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact (hi.trans_le hab).le
  have heq : (Finset.univ.filter fun i : Fin d => a ≤ t i ∧ t i ≤ b) = B \ A := by
    ext i
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, not_lt]
    exact and_comm
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  have hcR : ((B \ A).card : ℝ) + (A.card : ℝ) = (B.card : ℝ) := by exact_mod_cast hc
  rw [heq]
  change ((B \ A).card : ℝ) = (B.card : ℝ) - A.card
  linarith

theorem hasIntervalDiscrepancyLE_of_count_bounds {d : ℕ} {t : Fin d → ℝ} {η : ℝ}
    (hLE : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |((Finset.univ.filter fun i : Fin d => t i ≤ u).card : ℝ) / d - u| ≤ η)
    (hLT : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |((Finset.univ.filter fun i : Fin d => t i < u).card : ℝ) / d - u| ≤ η) :
    HasIntervalDiscrepancyLE t (2 * η) := by
  intro a b ha hab hb
  have hle := abs_le.mp (hLE b ⟨ha.trans hab, hb⟩)
  have hlt := abs_le.mp (hLT a ⟨ha, hab.trans hb⟩)
  rw [card_closed_interval_eq_count_sub t hab, sub_div]
  apply abs_le.mpr
  constructor <;> linarith

theorem hasIntervalDiscrepancyLE_of_grid {d q : ℕ} (hq : 0 < q) {t : Fin d → ℝ} {η : ℝ}
    (hLE : ∀ k : Fin (q + 1),
      |((Finset.univ.filter fun i : Fin d => t i ≤ (k.val : ℝ) / q).card : ℝ) / d -
        (k.val : ℝ) / q| ≤ η)
    (hLT : ∀ k : Fin (q + 1),
      |((Finset.univ.filter fun i : Fin d => t i < (k.val : ℝ) / q).card : ℝ) / d -
        (k.val : ℝ) / q| ≤ η) :
    HasIntervalDiscrepancyLE t (2 * (η + 1 / q)) := by
  apply hasIntervalDiscrepancyLE_of_count_bounds
  · intro u hu
    exact abs_sub_le_of_monotone_grid hq (monotone_count_le_div t) hLE hu
  · intro u hu
    exact abs_sub_le_of_monotone_grid hq (monotone_count_lt_div t) hLT hu

end DirichletL

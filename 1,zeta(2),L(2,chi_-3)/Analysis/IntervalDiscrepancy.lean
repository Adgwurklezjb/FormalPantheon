import Comparator.Statement

/-!
Closed-interval discrepancy in CDT v2, supplied TeX 3180-3187,
and its order-statistic consequences at TeX 3918-3948.
Counts retain both endpoints and repeated coordinate values.
-/

namespace DirichletL

/-- Every closed subinterval of `[0,1]` has empirical mass within `ε` of its length. -/
def HasIntervalDiscrepancyLE {d : ℕ} (t : Fin d → ℝ) (ε : ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    |((Finset.univ.filter fun i : Fin d => a ≤ t i ∧ t i ≤ b).card : ℝ) / d - (b - a)| ≤ ε

variable {d : ℕ} {t : Fin d → ℝ} {ε η : ℝ}

theorem HasIntervalDiscrepancyLE.mono (h : HasIntervalDiscrepancyLE t ε) (hεη : ε ≤ η) :
    HasIntervalDiscrepancyLE t η := by
  intro a b ha hab hb
  exact (h a b ha hab hb).trans hεη

theorem HasIntervalDiscrepancyLE.comp_perm (h : HasIntervalDiscrepancyLE t ε)
    (σ : Equiv.Perm (Fin d)) : HasIntervalDiscrepancyLE (t ∘ σ) ε := by
  classical
  intro a b ha hab hb
  have hc : (Finset.univ.filter fun i : Fin d => a ≤ t (σ i) ∧ t (σ i) ≤ b).card =
      (Finset.univ.filter fun i : Fin d => a ≤ t i ∧ t i ≤ b).card := by
    apply Finset.card_equiv σ
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change |((Finset.univ.filter fun i : Fin d => a ≤ t (σ i) ∧ t (σ i) ≤ b).card : ℝ) /
    d - (b - a)| ≤ ε
  rw [hc]
  exact h a b ha hab hb

theorem HasIntervalDiscrepancyLE.count_le (h : HasIntervalDiscrepancyLE t ε)
    (hd : 0 < d) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ((Finset.univ.filter fun i : Fin d => a ≤ t i ∧ t i ≤ b).card : ℝ) ≤
      (b - a + ε) * d := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hh := (abs_le.mp (h a b ha hab hb)).2
  apply (div_le_iff₀ hdR).mp
  linarith

theorem HasIntervalDiscrepancyLE.count_ge (h : HasIntervalDiscrepancyLE t ε)
    (hd : 0 < d) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (b - a - ε) * d ≤
      ((Finset.univ.filter fun i : Fin d => a ≤ t i ∧ t i ≤ b).card : ℝ) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hh := (abs_le.mp (h a b ha hab hb)).1
  apply (le_div_iff₀ hdR).mp
  linarith

theorem HasIntervalDiscrepancyLE.coordinate_lower (h : HasIntervalDiscrepancyLE t ε)
    (hcube : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) (hmono : Monotone t) (i : Fin d) :
    (i.val + 1 : ℕ) / (d : ℝ) - ε ≤ t i := by
  classical
  have hd : 0 < d := by have hi := i.isLt; omega
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hc : i.val + 1 ≤
      (Finset.univ.filter fun j : Fin d => 0 ≤ t j ∧ t j ≤ t i).card := by
    calc
      _ = (Finset.Iic i).card := (Fin.card_Iic i).symm
      _ ≤ _ := by
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(hcube j).1, hmono (Finset.mem_Iic.mp hj)⟩
  have hcR : ((i.val + 1 : ℕ) : ℝ) ≤
      ((Finset.univ.filter fun j : Fin d => 0 ≤ t j ∧ t j ≤ t i).card : ℝ) := by
    exact_mod_cast hc
  have hb := h.count_le hd (le_refl (0 : ℝ)) (hcube i).1 (hcube i).2
  apply sub_le_iff_le_add.mpr
  apply (div_le_iff₀ hdR).mpr
  exact hcR.trans (by simpa only [sub_zero] using hb)

theorem HasIntervalDiscrepancyLE.coordinate_upper (h : HasIntervalDiscrepancyLE t ε)
    (hcube : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) (hmono : Monotone t) (i : Fin d) :
    t i ≤ (i.val : ℝ) / d + ε := by
  classical
  have hd : 0 < d := by have hi := i.isLt; omega
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hc : d - i.val ≤
      (Finset.univ.filter fun j : Fin d => t i ≤ t j ∧ t j ≤ 1).card := by
    calc
      _ = (Finset.Ici i).card := (Fin.card_Ici i).symm
      _ ≤ _ := by
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hmono (Finset.mem_Ici.mp hj), (hcube j).2⟩
  have hcR : (d : ℝ) - i.val ≤
      ((Finset.univ.filter fun j : Fin d => t i ≤ t j ∧ t j ≤ 1).card : ℝ) := by
    have hc' : ((d - i.val : ℕ) : ℝ) ≤
        ((Finset.univ.filter fun j : Fin d => t i ≤ t j ∧ t j ≤ 1).card : ℝ) := by
      exact_mod_cast hc
    simpa only [Nat.cast_sub (Nat.le_of_lt i.isLt)] using hc'
  have hb := h.count_le hd (hcube i).1 (hcube i).2 (le_refl (1 : ℝ))
  apply sub_le_iff_le_add.mp
  apply (le_div_iff₀ hdR).mpr
  nlinarith [hcR.trans hb]

theorem HasIntervalDiscrepancyLE.exists_monotone_perm_bounds
    (h : HasIntervalDiscrepancyLE t ε) (hcube : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) :
    ∃ σ : Equiv.Perm (Fin d), Monotone (t ∘ σ) ∧
      ∀ i : Fin d, (i.val + 1 : ℕ) / (d : ℝ) - ε ≤ t (σ i) ∧
        t (σ i) ≤ (i.val : ℝ) / d + ε := by
  refine ⟨Tuple.sort t, Tuple.monotone_sort t, ?_⟩
  have hs := h.comp_perm (Tuple.sort t)
  have hcube' : ∀ i, (t ∘ Tuple.sort t) i ∈ Set.Icc (0 : ℝ) 1 :=
    fun i => hcube (Tuple.sort t i)
  intro i
  exact ⟨hs.coordinate_lower hcube' (Tuple.monotone_sort t) i,
    hs.coordinate_upper hcube' (Tuple.monotone_sort t) i⟩

end DirichletL

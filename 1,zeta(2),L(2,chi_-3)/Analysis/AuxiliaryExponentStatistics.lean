import Analysis.IntervalDiscrepancy
import Arithmetic.BalancedMapCardinality

/-!
Meanings and endpoint checks were recorded before these bodies in
CDT v2, supplied TeX 3879-3948 and the denominator application 4304-4404.
-/

namespace DirichletL

open scoped Classical

theorem unit_interval_of_strict_nat_cutoff {d L : ℕ} {R : ℝ}
    (hR : 0 < R) (hLR : (L : ℝ) ≤ R + 1) (n : Fin d → ℕ)
    (hn : ∀ j, n j < L) : ∀ j, (n j : ℝ) / R ∈ Set.Icc (0 : ℝ) 1 := by
  intro j
  have hj : (n j : ℝ) + 1 ≤ L := by exact_mod_cast Nat.succ_le_iff.mpr (hn j)
  refine ⟨div_nonneg (Nat.cast_nonneg _) hR.le, (div_le_one hR).mpr ?_⟩
  linarith

theorem HasIntervalDiscrepancyLE.sum_subset_bounds {d : ℕ} {t : Fin d → ℝ} {ε : ℝ}
    (h : HasIntervalDiscrepancyLE t ε) (hcube : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1)
    (hmono : Monotone t) (s : Finset (Fin d)) :
    (∑ i ∈ s, ((i : ℝ) + 1) / d) - s.card * ε ≤ ∑ i ∈ s, t i ∧
      (∑ i ∈ s, t i) ≤ (∑ i ∈ s, (i : ℝ) / d) + s.card * ε := by
  constructor
  · have hs := Finset.sum_le_sum (fun i (_ : i ∈ s) => h.coordinate_lower hcube hmono i)
    simpa only [Nat.cast_add, Nat.cast_one, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul] using hs
  · have hs := Finset.sum_le_sum (fun i (_ : i ∈ s) => h.coordinate_upper hcube hmono i)
    simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] using hs

theorem exists_sorted_auxiliary_exponent_cap {h D L : ℕ} {δ ε : ℝ}
    (hh : 0 < h) (hD : 0 < D) (hδ : 0 < δ) (hδε : δ < ε) (hε1 : ε ≤ 1)
    (n : Fin (14 * h) → ℕ) (hn : ∀ j, n j < L)
    (hLR : (L : ℝ) ≤ (14 + δ) * D + 1)
    (hdis : HasIntervalDiscrepancyLE (fun j => (n j : ℝ) / ((14 + δ) * D)) ε) :
    ∃ σ : Equiv.Perm (Fin (14 * h)), Monotone (n ∘ σ) ∧
      ∀ i : Fin (14 * h), (n (σ i) : ℝ) ≤
        D * (16 * ε + ((i : ℝ) + 1) / h) := by
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hdR : 0 < ((14 * h : ℕ) : ℝ) := by positivity
  have hR : 0 < (14 + δ) * (D : ℝ) := mul_pos (by linarith) hDR
  have hcube := unit_interval_of_strict_nat_cutoff hR hLR n hn
  obtain ⟨σ, hmono, hb⟩ := hdis.exists_monotone_perm_bounds hcube
  refine ⟨σ, ?_, ?_⟩
  · intro i j hij
    have hs : (n (σ i) : ℝ) ≤ n (σ j) :=
      (div_le_div_iff_of_pos_right hR).mp (hmono hij)
    exact_mod_cast hs
  · intro i
    have hfrac1 : (i : ℝ) / ((14 * h : ℕ) : ℝ) ≤ 1 := by
      apply (div_le_one hdR).mpr
      exact_mod_cast Nat.le_of_lt i.isLt
    have hgrid : (i : ℝ) / ((14 * h : ℕ) : ℝ) * 14 = (i : ℝ) / h := by
      push_cast
      field_simp
    have hε0 : 0 ≤ ε := (hδ.trans hδε).le
    have herr : ((i : ℝ) / ((14 * h : ℕ) : ℝ) + ε) * (14 + δ) ≤
        (i : ℝ) / h + 16 * ε := by
      nlinarith [mul_le_mul_of_nonneg_left hfrac1 hδ.le,
        mul_le_mul_of_nonneg_right (hδε.le.trans hε1) hε0]
    have hi : (i : ℝ) / h ≤ ((i : ℝ) + 1) / h :=
      div_le_div_of_nonneg_right (by linarith) hhR.le
    calc
      (n (σ i) : ℝ) ≤ ((i : ℝ) / ((14 * h : ℕ) : ℝ) + ε) * ((14 + δ) * D) :=
        (div_le_iff₀ hR).mp (hb i).2
      _ = (((i : ℝ) / ((14 * h : ℕ) : ℝ) + ε) * (14 + δ)) * D := by ring
      _ ≤ ((i : ℝ) / h + 16 * ε) * D := mul_le_mul_of_nonneg_right herr hDR.le
      _ ≤ D * (16 * ε + ((i : ℝ) + 1) / h) := by nlinarith

theorem balancedSpeciesIndices_comp_perm {m h : ℕ} {s : Fin (m * h) → Fin m}
    (hs : s ∈ balancedSpeciesIndices m h) (σ : Equiv.Perm (Fin (m * h))) :
    s ∘ σ ∈ balancedSpeciesIndices m h := by
  simp only [balancedSpeciesIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  intro i
  have hc : (Finset.univ.filter (fun j : Fin (m * h) => s (σ j) = i)).card =
      (Finset.univ.filter (fun j : Fin (m * h) => s j = i)).card := by
    apply Finset.card_equiv σ
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hc.trans (hs i)

end DirichletL

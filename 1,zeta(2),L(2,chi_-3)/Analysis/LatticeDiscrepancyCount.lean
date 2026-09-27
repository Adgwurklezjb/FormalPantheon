import Analysis.FiniteDiscrepancyCount
import Analysis.LatticePopulation

/-!
Exponential bounds for the literal finite lattice tuples used in the
auxiliary construction of CDT v2, supplied TeX 3950-4004.
-/

namespace DirichletL

open Real
open scoped Classical

theorem card_bad_lattice_discrepancy_div_le {L d q : ℕ} {R ε : ℝ}
    (hR : 0 < R) (hRL : R ≤ L) (hLR : (L : ℝ) ≤ R + 1)
    (hd : 0 < d) (hq : 0 < q) (hε : 0 < ε)
    (hmesh : 1 / (q : ℝ) ≤ ε / 8) (hpop : 1 / (L : ℝ) ≤ ε / 8) :
    ((Finset.univ.filter fun t : Fin d → Fin L =>
      ¬HasIntervalDiscrepancyLE (fun i => ((t i).val : ℝ) / R) ε).card : ℝ) / (L : ℝ) ^ d ≤
      4 * (q + 1 : ℕ) * exp (-ε ^ 2 * d / 128) := by
  have hL : 0 < L := by exact_mod_cast hR.trans_le hRL
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hu (k : Fin (q + 1)) : (k.val : ℝ) / q ∈ Set.Icc (0 : ℝ) 1 := by
    have hk : (k.val : ℝ) ≤ q := by exact_mod_cast Nat.le_of_lt_succ k.isLt
    exact ⟨div_nonneg (Nat.cast_nonneg _) hqR.le,
      (div_le_iff₀ hqR).mpr (by simpa only [one_mul] using hk)⟩
  have h := card_bad_discrepancy_div_le_of_grid_bias hd hq
    (fun i : Fin L => (i.val : ℝ) / R) hε hmesh
    (fun k => by simpa only [Fintype.card_fin] using
      (abs_lattice_population_le_sub_le hR hRL hLR (hu k)).trans hpop)
    (fun k => by simpa only [Fintype.card_fin] using
      (abs_lattice_population_lt_sub_le hR hRL hLR (hu k)).trans hpop)
  simpa only [Fintype.card_fin, Function.comp_def] using h

theorem one_sub_le_card_good_lattice_discrepancy_div {L d q : ℕ} {R ε : ℝ}
    (hR : 0 < R) (hRL : R ≤ L) (hLR : (L : ℝ) ≤ R + 1)
    (hd : 0 < d) (hq : 0 < q) (hε : 0 < ε)
    (hmesh : 1 / (q : ℝ) ≤ ε / 8) (hpop : 1 / (L : ℝ) ≤ ε / 8) :
    1 - 4 * (q + 1 : ℕ) * exp (-ε ^ 2 * d / 128) ≤
      ((Finset.univ.filter fun t : Fin d → Fin L =>
        HasIntervalDiscrepancyLE (fun i => ((t i).val : ℝ) / R) ε).card : ℝ) / (L : ℝ) ^ d := by
  have hL : 0 < L := by exact_mod_cast hR.trans_le hRL
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hu (k : Fin (q + 1)) : (k.val : ℝ) / q ∈ Set.Icc (0 : ℝ) 1 := by
    have hk : (k.val : ℝ) ≤ q := by exact_mod_cast Nat.le_of_lt_succ k.isLt
    exact ⟨div_nonneg (Nat.cast_nonneg _) hqR.le,
      (div_le_iff₀ hqR).mpr (by simpa only [one_mul] using hk)⟩
  have h := one_sub_le_card_good_discrepancy_div_of_grid_bias hd hq
    (fun i : Fin L => (i.val : ℝ) / R) hε hmesh
    (fun k => by simpa only [Fintype.card_fin] using
      (abs_lattice_population_le_sub_le hR hRL hLR (hu k)).trans hpop)
    (fun k => by simpa only [Fintype.card_fin] using
      (abs_lattice_population_lt_sub_le hR hRL hLR (hu k)).trans hpop)
  simpa only [Fintype.card_fin, Function.comp_def] using h

end DirichletL

import Arithmetic.BalancedMapCardinality
import Analysis.LatticeDiscrepancyCount

/-!
Finite free and constrained coefficient indices for CDT v2,
supplied TeX 3950-4004. The upper cube is explicit; its zero-estimate
application and the nonzero auxiliary function are separate proofs.
-/

noncomputable section

namespace DirichletL

open scoped Classical

/-- Balanced species paired with polynomial exponents satisfying the discrepancy bound. -/
def auxiliaryFreeIndices (m h D : ℕ) (ε : ℝ) :
    Finset ((Fin (m * h) → Fin m) × (Fin (m * h) → Fin D)) :=
  (balancedSpeciesIndices m h).product (Finset.univ.filter fun t : Fin (m * h) → Fin D =>
    HasIntervalDiscrepancyLE (fun i => ((t i).val : ℝ) / D) ε)

theorem mem_auxiliaryFreeIndices {m h D : ℕ} {ε : ℝ}
    {p : (Fin (m * h) → Fin m) × (Fin (m * h) → Fin D)} :
    p ∈ auxiliaryFreeIndices m h D ε ↔ p.1 ∈ balancedSpeciesIndices m h ∧
      HasIntervalDiscrepancyLE (fun i => ((p.2 i).val : ℝ) / D) ε := by
  simp [auxiliaryFreeIndices]

theorem card_auxiliaryFreeIndices (m h D : ℕ) (ε : ℝ) :
    (auxiliaryFreeIndices m h D ε).card = (balancedSpeciesIndices m h).card *
      (Finset.univ.filter fun t : Fin (m * h) → Fin D =>
        HasIntervalDiscrepancyLE (fun i => ((t i).val : ℝ) / D) ε).card :=
  Finset.card_product _ _

theorem card_auxiliaryFreeIndices_lower {m h D q : ℕ} {ε : ℝ}
    (hd : 0 < m * h) (hD : 0 < D) (hq : 0 < q) (hε : 0 < ε)
    (hmesh : 1 / (q : ℝ) ≤ ε / 8) (hpop : 1 / (D : ℝ) ≤ ε / 8) :
    (1 - 4 * (q + 1 : ℕ) * Real.exp (-ε ^ 2 * (m * h : ℕ) / 128)) *
      (balancedSpeciesIndices m h).card * (D : ℝ) ^ (m * h) ≤
      (auxiliaryFreeIndices m h D ε).card := by
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hg := one_sub_le_card_good_lattice_discrepancy_div hDR (le_refl (D : ℝ))
    (by linarith : (D : ℝ) ≤ D + 1) hd hq hε hmesh hpop
  have hg' := (le_div_iff₀ (pow_pos hDR (m * h))).mp hg
  have hb := mul_le_mul_of_nonneg_left hg'
    (Nat.cast_nonneg (balancedSpeciesIndices m h).card :
      (0 : ℝ) ≤ (balancedSpeciesIndices m h).card)
  rw [card_auxiliaryFreeIndices]
  simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using hb

/-- Small-cube and discrepancy constraints inside one explicit finite upper cube. -/
def auxiliaryConstraintIndices (d L : ℕ) (R S ε : ℝ) : Finset (Fin d → Fin L) :=
  Finset.univ.filter fun t => (∀ i, ((t i).val : ℝ) ≤ S) ∨
    ¬HasIntervalDiscrepancyLE (fun i => ((t i).val : ℝ) / R) ε

theorem mem_auxiliaryConstraintIndices {d L : ℕ} {R S ε : ℝ} {t : Fin d → Fin L} :
    t ∈ auxiliaryConstraintIndices d L R S ε ↔ (∀ i, ((t i).val : ℝ) ≤ S) ∨
      ¬HasIntervalDiscrepancyLE (fun i => ((t i).val : ℝ) / R) ε := by
  simp [auxiliaryConstraintIndices]

theorem card_small_lattice_cube (d L : ℕ) (S : ℝ) :
    (Finset.univ.filter fun t : Fin d → Fin L => ∀ i, ((t i).val : ℝ) ≤ S).card =
      (Finset.univ.filter fun i : Fin L => (i.val : ℝ) ≤ S).card ^ d := by
  have he : (Finset.univ.filter fun t : Fin d → Fin L => ∀ i, ((t i).val : ℝ) ≤ S) =
      Fintype.piFinset (fun _ : Fin d =>
        Finset.univ.filter fun i : Fin L => (i.val : ℝ) ≤ S) := by
    ext t
    simp
  rw [he, Fintype.card_piFinset_const]

theorem card_auxiliaryConstraintIndices_le {d L q : ℕ} {R S ε : ℝ}
    (hR : 0 < R) (hRL : R ≤ L) (hLR : (L : ℝ) ≤ R + 1)
    (hS : S ∈ Set.Icc (0 : ℝ) L) (hd : 0 < d) (hq : 0 < q) (hε : 0 < ε)
    (hmesh : 1 / (q : ℝ) ≤ ε / 8) (hpop : 1 / (L : ℝ) ≤ ε / 8) :
    ((auxiliaryConstraintIndices d L R S ε).card : ℝ) ≤
      (S + 1) ^ d + 4 * (q + 1 : ℕ) * Real.exp (-ε ^ 2 * d / 128) * (L : ℝ) ^ d := by
  have hL : 0 < (L : ℝ) := hR.trans_le hRL
  have hb := (div_le_iff₀ (pow_pos hL d)).mp
    (card_bad_lattice_discrepancy_div_le hR hRL hLR hd hq hε hmesh hpop)
  have hs : ((Finset.univ.filter fun t : Fin d → Fin L =>
      ∀ i, ((t i).val : ℝ) ≤ S).card : ℝ) ≤ (S + 1) ^ d := by
    rw [card_small_lattice_cube, Nat.cast_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (cast_card_fin_le_bounds hS).2 d
  have hu : ((auxiliaryConstraintIndices d L R S ε).card : ℝ) ≤
      (Finset.univ.filter fun t : Fin d → Fin L => ∀ i, ((t i).val : ℝ) ≤ S).card +
      (Finset.univ.filter fun t : Fin d → Fin L =>
        ¬HasIntervalDiscrepancyLE (fun i => ((t i).val : ℝ) / R) ε).card := by
    unfold auxiliaryConstraintIndices
    rw [Finset.filter_or]
    exact_mod_cast Finset.card_union_le
      (Finset.univ.filter fun t : Fin d → Fin L => ∀ i, ((t i).val : ℝ) ≤ S)
      (Finset.univ.filter fun t : Fin d → Fin L =>
        ¬HasIntervalDiscrepancyLE (fun i => ((t i).val : ℝ) / R) ε)
  linarith

end DirichletL

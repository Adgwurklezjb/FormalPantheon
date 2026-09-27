import Comparator.Statement

/-!
Exact lattice population errors for the finite count in CDT v2,
supplied TeX 3950-4004. Both endpoint conventions retain their integer counts.
-/

namespace DirichletL

theorem cast_card_fin_le_bounds {L : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) L) :
    x ≤ ((Finset.univ.filter fun i : Fin L => (i.val : ℝ) ≤ x).card : ℝ) ∧
      ((Finset.univ.filter fun i : Fin L => (i.val : ℝ) ≤ x).card : ℝ) ≤ x + 1 := by
  have heq : (Finset.univ.filter fun i : Fin L => (i.val : ℝ) ≤ x) =
      Finset.univ.filter (fun i : Fin L => i.val < min L (⌊x⌋₊ + 1)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_min_iff, i.isLt,
      Nat.lt_add_one_iff, Nat.le_floor_iff hx.1]
  have hc : (Finset.univ.filter fun i : Fin L => (i.val : ℝ) ≤ x).card =
      min L (⌊x⌋₊ + 1) := by
    rw [heq, ← Fintype.card_subtype]
    exact Fintype.card_fin_lt_of_le (Nat.min_le_left _ _)
  rw [hc]
  simp only [Nat.cast_min, Nat.cast_add, Nat.cast_one]
  exact ⟨le_min hx.2 (Nat.lt_floor_add_one x).le,
    (min_le_right _ _).trans (add_le_add_right (Nat.floor_le hx.1) 1)⟩

theorem cast_card_fin_lt_bounds {L : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) L) :
    x ≤ ((Finset.univ.filter fun i : Fin L => (i.val : ℝ) < x).card : ℝ) ∧
      ((Finset.univ.filter fun i : Fin L => (i.val : ℝ) < x).card : ℝ) ≤ x + 1 := by
  have heq : (Finset.univ.filter fun i : Fin L => (i.val : ℝ) < x) =
      Finset.univ.filter (fun i : Fin L => i.val < ⌈x⌉₊) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.lt_ceil]
  have hc : (Finset.univ.filter fun i : Fin L => (i.val : ℝ) < x).card = ⌈x⌉₊ := by
    rw [heq, ← Fintype.card_subtype]
    exact Fintype.card_fin_lt_of_le (Nat.ceil_le.mpr hx.2)
  rw [hc]
  exact ⟨Nat.le_ceil x, (Nat.ceil_lt_add_one hx.1).le⟩

theorem abs_lattice_population_le_sub_le {L : ℕ} {R u : ℝ} (hR : 0 < R)
    (hRL : R ≤ L) (hLR : (L : ℝ) ≤ R + 1) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    |((Finset.univ.filter fun i : Fin L => (i.val : ℝ) / R ≤ u).card : ℝ) / L - u| ≤
      1 / (L : ℝ) := by
  have hL : 0 < (L : ℝ) := hR.trans_le hRL
  have hx : u * R ≤ (L : ℝ) :=
    (show u * R ≤ R by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hu.2 hR.le).trans hRL
  let C : ℝ := ((Finset.univ.filter fun i : Fin L => (i.val : ℝ) ≤ u * R).card : ℝ)
  have hcount : u * R ≤ C ∧ C ≤ u * R + 1 :=
    cast_card_fin_le_bounds ⟨mul_nonneg hu.1 hR.le, hx⟩
  have ha : |C - u * L| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [hcount.1, hcount.2, hu.2, mul_le_mul_of_nonneg_left hRL hu.1,
      mul_le_mul_of_nonneg_left hLR hu.1]
  have heq : C / (L : ℝ) - u = (C - u * L) / L := by
    field_simp [hL.ne']
  simp only [div_le_iff₀ hR]
  change |C / (L : ℝ) - u| ≤ 1 / (L : ℝ)
  rw [heq, abs_div, abs_of_pos hL]
  exact div_le_div_of_nonneg_right ha hL.le

theorem abs_lattice_population_lt_sub_le {L : ℕ} {R u : ℝ} (hR : 0 < R)
    (hRL : R ≤ L) (hLR : (L : ℝ) ≤ R + 1) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    |((Finset.univ.filter fun i : Fin L => (i.val : ℝ) / R < u).card : ℝ) / L - u| ≤
      1 / (L : ℝ) := by
  have hL : 0 < (L : ℝ) := hR.trans_le hRL
  have hx : u * R ≤ (L : ℝ) :=
    (show u * R ≤ R by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hu.2 hR.le).trans hRL
  let C : ℝ := ((Finset.univ.filter fun i : Fin L => (i.val : ℝ) < u * R).card : ℝ)
  have hcount : u * R ≤ C ∧ C ≤ u * R + 1 :=
    cast_card_fin_lt_bounds ⟨mul_nonneg hu.1 hR.le, hx⟩
  have ha : |C - u * L| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [hcount.1, hcount.2, hu.2, mul_le_mul_of_nonneg_left hRL hu.1,
      mul_le_mul_of_nonneg_left hLR hu.1]
  have heq : C / (L : ℝ) - u = (C - u * L) / L := by
    field_simp [hL.ne']
  simp only [div_lt_iff₀ hR]
  change |C / (L : ℝ) - u| ≤ 1 / (L : ℝ)
  rw [heq, abs_div, abs_of_pos hL]
  exact div_le_div_of_nonneg_right ha hL.le

end DirichletL

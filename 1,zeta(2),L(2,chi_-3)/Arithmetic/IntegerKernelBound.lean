import Comparator.Statement

/-!
The native Siegel lemma with an entrywise height and a prescribed
Dirichlet exponent, for CDT v2, supplied TeX 3986-4004.
-/

namespace DirichletL

attribute [local instance] Matrix.seminormedAddCommGroup

theorem exists_int_kernel_of_card_ratio_le {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α β ℤ) (hM : 0 < Fintype.card α) (hMN : Fintype.card α < Fintype.card β)
    {η H : ℝ} (hratio : (Fintype.card α : ℝ) / (Fintype.card β - Fintype.card α : ℕ) ≤ η)
    (hH : 1 ≤ H) (hA : ∀ i j, |(A i j : ℝ)| ≤ H) :
    ∃ t : β → ℤ, t ≠ 0 ∧ A.mulVec t = 0 ∧
      ∀ j, |(t j : ℝ)| ≤ Real.exp (η * (Real.log (Fintype.card β) + Real.log H)) := by
  classical
  have hN : 0 < Fintype.card β := hM.trans hMN
  have hNR : 0 < (Fintype.card β : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ Fintype.card β := by exact_mod_cast Nat.succ_le_iff.mpr hN
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hη : 0 ≤ η := (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans hratio
  have hnorm : ‖A‖ ≤ H := (Matrix.norm_le_iff hHpos.le).mpr (by
    intro i j
    simpa only [Int.norm_eq_abs] using hA i j)
  have hbase : (1 : ℝ) ≤ Fintype.card β * max 1 ‖A‖ :=
    one_le_mul_of_one_le_of_one_le hN1 (le_max_left _ _)
  have hratio' : (Fintype.card α : ℝ) / ((Fintype.card β : ℝ) - Fintype.card α) ≤ η := by
    simpa only [Nat.cast_sub hMN.le] using hratio
  obtain ⟨t, ht, hAt, hsize⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le A hMN hM
  have hsize' : ‖t‖ ≤ Real.exp (η * (Real.log (Fintype.card β) + Real.log H)) := by
    calc
      _ ≤ ((Fintype.card β : ℝ) * max 1 ‖A‖) ^
          ((Fintype.card α : ℝ) / ((Fintype.card β : ℝ) - Fintype.card α)) := hsize
      _ ≤ ((Fintype.card β : ℝ) * max 1 ‖A‖) ^ η :=
        Real.rpow_le_rpow_of_exponent_le hbase hratio'
      _ ≤ ((Fintype.card β : ℝ) * H) ^ η :=
        Real.rpow_le_rpow (zero_le_one.trans hbase)
          (mul_le_mul_of_nonneg_left (max_le hH hnorm) hNR.le) hη
      _ = _ := by
        rw [Real.rpow_def_of_pos (mul_pos hNR hHpos), Real.log_mul hNR.ne' hHpos.ne']
        congr 1
        ring
  refine ⟨t, ht, hAt, fun j => ?_⟩
  simpa only [Int.norm_eq_abs] using (norm_le_pi_norm t j).trans hsize'

end DirichletL

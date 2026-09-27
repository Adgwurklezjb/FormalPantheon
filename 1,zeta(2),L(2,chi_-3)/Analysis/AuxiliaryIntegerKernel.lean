import Analysis.AuxiliaryDimensionComparison
import Analysis.AuxiliarySizeBounds
import Arithmetic.IntegerKernelBound

/-!
Small integer kernel vectors on the actual auxiliary index sets in
CDT v2, supplied TeX 3950-4004. The coefficient matrix and its height
remain explicit inputs; nonvanishing of a formal function is separate.
-/

namespace DirichletL

open Filter Set
open scoped Classical Topology

theorem exists_auxiliary_integer_kernel {m : ℕ} (hm : 1 < m) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ δ < m ∧ ∀ K : ℝ, 0 ≤ K → ∀ ζ : ℝ, 0 < ζ →
      ∀ᶠ h : ℕ in atTop, ∀ᶠ D : ℕ in atTop, ∀ L : ℕ,
        ((m : ℝ) + δ) * D ≤ L → (L : ℝ) ≤ ((m : ℝ) + δ) * D + 1 →
        ∀ A : Matrix ↥(auxiliaryConstraintIndices (m * h) L
          (((m : ℝ) + δ) * D) (((m : ℝ) - δ) * D) ε)
          ↥(auxiliaryFreeIndices m h D ε) ℤ,
          (∀ i j, |(A i j : ℝ)| ≤ Real.exp (K * (m * h : ℕ) * D)) →
          ∃ t : ↥(auxiliaryFreeIndices m h D ε) → ℤ, t ≠ 0 ∧ A.mulVec t = 0 ∧
            ∀ j, |(t j : ℝ)| ≤ Real.exp (ζ * (m * h : ℕ) * D) := by
  obtain ⟨δ, hδ, hδε, hδm, hcount⟩ := exists_auxiliary_dimension_comparison hm hε
  refine ⟨δ, hδ, hδε, hδm, fun K hK ζ hζ => ?_⟩
  let η : ℝ := ζ / (1 + K)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηeq : η * (1 + K) = ζ := div_mul_cancel₀ _ (by positivity)
  have hm0 : 0 < m := by omega
  filter_upwards [hcount η hη, eventually_gt_atTop (0 : ℕ)] with h hcountH hh
  filter_upwards [hcountH, eventually_log_card_auxiliaryFreeIndices_le hm0 ε]
    with D hcountD hsizeD
  intro L hRL hLR A hA
  have hD : 0 < D := hsizeD.1
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hdR : 0 < ((m * h : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hm0 hh
  have hL : 0 < L := by exact_mod_cast (mul_pos (by linarith : (0 : ℝ) < m + δ) hDR).trans_le hRL
  have hS : 0 ≤ ((m : ℝ) - δ) * D := mul_nonneg (by linarith) hDR.le
  obtain ⟨hN, hMN, hratio⟩ := hcountD L hRL hLR
  have hM := card_auxiliaryConstraintIndices_pos (d := m * h)
    (R := ((m : ℝ) + δ) * D) (ε := ε) hL hS
  have hH : 1 ≤ Real.exp (K * (m * h : ℕ) * D) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (mul_nonneg hK hdR.le) hDR.le)
  obtain ⟨t, ht, hAt, hbound⟩ := exists_int_kernel_of_card_ratio_le A
    (by simpa only [Fintype.card_coe] using hM)
    (by simpa only [Fintype.card_coe] using hMN)
    (by simpa only [Fintype.card_coe] using hratio) hH hA
  have hlog := hsizeD.2 h hN
  have hexponent : η * (Real.log ((auxiliaryFreeIndices m h D ε).card : ℝ) +
      K * (m * h : ℕ) * D) ≤ ζ * (m * h : ℕ) * D := by
    calc
      _ ≤ η * ((1 + K) * (m * h : ℕ) * D) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hη.le
      _ = (η * (1 + K)) * (m * h : ℕ) * D := by ring
      _ = _ := by rw [hηeq]
  refine ⟨t, ht, hAt, fun j => ?_⟩
  have hj := hbound j
  simp only [Fintype.card_coe, Real.log_exp] at hj
  exact hj.trans (Real.exp_le_exp.mpr hexponent)

end DirichletL

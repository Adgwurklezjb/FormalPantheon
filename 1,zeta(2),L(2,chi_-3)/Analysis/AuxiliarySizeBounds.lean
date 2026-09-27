import Analysis.AuxiliaryParameterIndices
import Arithmetic.BalancedCardinalityAsymptotic

/-!
Literal row positivity and column-size estimates for the Siegel step
in CDT v2, supplied TeX 3980-4004. Integer endpoints remain explicit.
-/

namespace DirichletL

open Filter Set
open scoped Classical Topology

theorem card_auxiliaryFreeIndices_le (m h D : ℕ) (ε : ℝ) :
    (auxiliaryFreeIndices m h D ε).card ≤ m ^ (m * h) * D ^ (m * h) := by
  rw [card_auxiliaryFreeIndices]
  apply Nat.mul_le_mul (card_balancedSpeciesIndices_le_pow m h)
  simpa using Finset.card_le_univ
    (Finset.univ.filter fun t : Fin (m * h) → Fin D =>
      HasIntervalDiscrepancyLE (fun i => ((t i).val : ℝ) / D) ε)

theorem card_auxiliaryConstraintIndices_pos {d L : ℕ} {R S ε : ℝ}
    (hL : 0 < L) (hS : 0 ≤ S) : 0 < (auxiliaryConstraintIndices d L R S ε).card := by
  apply Finset.card_pos.mpr
  refine ⟨fun _ => ⟨0, hL⟩, ?_⟩
  exact mem_auxiliaryConstraintIndices.mpr (Or.inl (fun _ => by simpa using hS))

theorem log_card_auxiliaryFreeIndices_le {m h D : ℕ} {ε : ℝ}
    (hm : 0 < m) (hD : 0 < D) (hN : 0 < (auxiliaryFreeIndices m h D ε).card) :
    Real.log ((auxiliaryFreeIndices m h D ε).card : ℝ) ≤
      (m * h : ℕ) * (Real.log m + Real.log D) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hNR : 0 < ((auxiliaryFreeIndices m h D ε).card : ℝ) := by exact_mod_cast hN
  have hbound : ((auxiliaryFreeIndices m h D ε).card : ℝ) ≤
      (m : ℝ) ^ (m * h) * (D : ℝ) ^ (m * h) := by
    exact_mod_cast card_auxiliaryFreeIndices_le m h D ε
  have hlog := Real.log_le_log hNR hbound
  rw [Real.log_mul (pow_pos hmR _).ne' (pow_pos hDR _).ne', Real.log_pow, Real.log_pow] at hlog
  nlinarith

theorem eventually_log_card_auxiliaryFreeIndices_le {m : ℕ} (hm : 0 < m) (ε : ℝ) :
    ∀ᶠ D : ℕ in atTop, 0 < D ∧ ∀ h : ℕ, 0 < (auxiliaryFreeIndices m h D ε).card →
      Real.log ((auxiliaryFreeIndices m h D ε).card : ℝ) ≤ (m * h : ℕ) * (D : ℝ) := by
  have hlog : Tendsto (fun D : ℕ => Real.log (D : ℝ) / D) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.one_mul, Nat.add_zero] using tendsto_log_nat_affine_div 1 0 (by decide)
  have hc : Tendsto (fun D : ℕ => Real.log (m : ℝ) / D) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun D : ℕ => (Real.log (m : ℝ) + Real.log (D : ℝ)) / D)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [← add_div, add_zero] using hc.add hlog
  filter_upwards [hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℕ)] with D hlogD hD
  refine ⟨hD, fun h hN => ?_⟩
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hlogs : Real.log (m : ℝ) + Real.log (D : ℝ) ≤ D := by
    have ht := (div_lt_iff₀ hDR).mp hlogD
    simpa only [one_mul] using ht.le
  exact (log_card_auxiliaryFreeIndices_le hm hD hN).trans
    (mul_le_mul_of_nonneg_left hlogs (Nat.cast_nonneg (m * h)))

end DirichletL

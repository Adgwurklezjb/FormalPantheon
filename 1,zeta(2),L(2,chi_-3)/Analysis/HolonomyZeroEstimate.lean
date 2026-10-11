import Analysis.RegularEulerZeroEstimate
import Analysis.HolonomyRegularEulerTransfer

/-!
The quantitative zero estimate for the actual fourteen series of CDT v2,
`lem_Shidlovsky` (TeX 2910-2935), `14functions`, and `typesA` (TeX 8280-8331).
Meanings, system selection, and edge checks are recorded before the proofs
-/

namespace DirichletL

theorem exists_linear_order_bound_holonomyRegularEuler (a b c : ℚ) :
    ∃ B : ℕ, ∀ (D : ℕ) (P : Fin 14 → Polynomial ℚ), 0 < D →
      (∀ i, (P i).natDegree < D) →
      (∑ i, (P i : PowerSeries ℚ) *
        holonomyRegularEulerSeries (symmetrizedDescent (a • hA + b • hB + c • hC)) i) ≠ 0 →
      (∑ i, (P i : PowerSeries ℚ) *
        holonomyRegularEulerSeries (symmetrizedDescent (a • hA + b • hB + c • hC)) i).order <
          (14 * D + B : ℕ) := by
  let g := symmetrizedDescent (a • hA + b • hB + c • hC)
  let C := holonomyRegularEulerNumerator g
    (Polynomial.C b * zagierDescendedForcingB + Polynomial.C c * zagierDescendedForcingC)
  have hq : holonomyRegularEulerDenominator.coeff 0 ≠ 0 := by
    rw [holonomyRegularEulerDenominator_constantCoeff]
    norm_num
  obtain ⟨B, hB⟩ := exists_linear_order_bound_of_cleared_euler_system
    holonomyRegularEulerDenominator C hq
  refine ⟨B, ?_⟩
  intro D P hD hP hF
  simpa only [Fintype.card_fin] using hB (holonomyRegularEulerSeries g) D P
    (fun i => holonomyRegularEuler_system a b c i) hD hP hF

theorem exists_linear_order_bound_cdtHolonomySeries (a b c : ℚ) :
    ∃ B : ℕ, ∀ (D : ℕ) (P : Fin 14 → Polynomial ℚ), 0 < D →
      (∀ i, (P i).natDegree < D) →
      (∑ i, (P i : PowerSeries ℚ) * cdtHolonomySeries a b c i) ≠ 0 →
      (∑ i, (P i : PowerSeries ℚ) * cdtHolonomySeries a b c i).order < (14 * D + B : ℕ) := by
  obtain ⟨B, hbound⟩ := exists_linear_order_bound_holonomyRegularEuler a b c
  refine ⟨42 + B, ?_⟩
  intro D P _hD hP hF
  obtain ⟨R, hR, he⟩ := exists_regularEuler_combination_cdtHolonomy a b c P D hP
  have hRne : (∑ i, (R i : PowerSeries ℚ) *
      holonomyRegularEulerSeries (symmetrizedDescent (a • hA + b • hB + c • hC)) i) ≠ 0 := by
    rw [← he]
    exact mul_ne_zero (pow_ne_zero 3 PowerSeries.X_ne_zero) hF
  have ho := hbound (D + 3) R (by omega) hR hRne
  rw [← he, PowerSeries.order_mul, PowerSeries.order_X_pow] at ho
  have hF' : (∑ i, (P i : PowerSeries ℚ) * cdtHolonomySeries a b c i).order <
      (14 * (D + 3) + B : ℕ) := (le_add_of_nonneg_left bot_le).trans_lt ho
  have hnat : 14 * (D + 3) + B = 14 * D + (42 + B) := by omega
  simpa only [hnat] using hF'

end DirichletL

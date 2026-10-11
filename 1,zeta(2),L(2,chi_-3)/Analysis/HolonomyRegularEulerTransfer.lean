import Analysis.HolonomyRegularEuler
import Analysis.PowerSeriesOrderBounds

/-!
CDT v2 `lem_Shidlovsky`, `14functions`, and `typesA`; meanings and edge
-/

noncomputable section

namespace DirichletL

open Polynomial

theorem holonomyRegularEulerWeights_le_three (i : Fin 14) :
    holonomyRegularEulerWeights i ≤ 3 := by
  fin_cases i <;> norm_num [holonomyRegularEulerWeights]

/-- Polynomial multipliers that express X cubed times a combination in the regular family. -/
def holonomyRegularEulerPolynomials (P : Fin 14 → ℚ[X]) : Fin 14 → ℚ[X] :=
  fun i => X ^ (3 - holonomyRegularEulerWeights i) * P i

theorem holonomyRegularEulerPolynomials_natDegree_lt (P : Fin 14 → ℚ[X])
    (D : ℕ) (hP : ∀ i, (P i).natDegree < D) (i : Fin 14) :
    (holonomyRegularEulerPolynomials P i).natDegree < D + 3 := by
  have h := Polynomial.natDegree_mul_le (p := (X : ℚ[X]) ^
    (3 - holonomyRegularEulerWeights i)) (q := P i)
  rw [Polynomial.natDegree_X_pow] at h
  change ((X : ℚ[X]) ^ (3 - holonomyRegularEulerWeights i) * P i).natDegree < _
  have hi := hP i
  omega

theorem holonomyRegularEuler_combination_eq (a b c : ℚ) (P : Fin 14 → ℚ[X]) :
    (PowerSeries.X : PowerSeries ℚ) ^ 3 *
        ∑ i, (P i : PowerSeries ℚ) * cdtFourteenSeries a b c i =
      ∑ i, (holonomyRegularEulerPolynomials P i : PowerSeries ℚ) *
        holonomyRegularEulerSeries (symmetrizedDescent (a • hA + b • hB + c • hC)) i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [holonomyRegularEulerSeries_eq]
  have hi := holonomyRegularEulerWeights_le_three i
  have hw : 3 - holonomyRegularEulerWeights i + holonomyRegularEulerWeights i = 3 := by omega
  simp only [holonomyRegularEulerPolynomials, coe_mul, coe_pow, coe_X]
  calc
    _ = ((PowerSeries.X : PowerSeries ℚ) ^ (3 - holonomyRegularEulerWeights i) *
        PowerSeries.X ^ holonomyRegularEulerWeights i) *
          (P i : PowerSeries ℚ) * cdtFourteenSeries a b c i := by
            rw [← pow_add, hw, mul_assoc]
    _ = _ := by ring

theorem holonomyRegularEuler_combination_ne_zero (a b c : ℚ) (P : Fin 14 → ℚ[X])
    (hP : ∑ i, (P i : PowerSeries ℚ) * cdtFourteenSeries a b c i ≠ 0) :
    ∑ i, (holonomyRegularEulerPolynomials P i : PowerSeries ℚ) *
      holonomyRegularEulerSeries (symmetrizedDescent (a • hA + b • hB + c • hC)) i ≠ 0 := by
  rw [← holonomyRegularEuler_combination_eq]
  exact mul_ne_zero (pow_ne_zero 3 PowerSeries.X_ne_zero) hP

theorem holonomyRegularEuler_order_combination (a b c : ℚ) (P : Fin 14 → ℚ[X]) :
    (∑ i, (holonomyRegularEulerPolynomials P i : PowerSeries ℚ) *
      holonomyRegularEulerSeries (symmetrizedDescent (a • hA + b • hB + c • hC)) i).order =
        3 + (∑ i, (P i : PowerSeries ℚ) * cdtFourteenSeries a b c i).order := by
  rw [← holonomyRegularEuler_combination_eq, PowerSeries.order_mul, PowerSeries.order_X_pow]
  norm_num

/-- The existing permutation from denominator-array order to the original family order. -/
def cdtHolonomyOrderEquiv : Fin 14 ≃ Fin 14 :=
  Equiv.ofBijective cdtHolonomyOrder
    ⟨cdtHolonomyOrder_injective, Finite.surjective_of_injective cdtHolonomyOrder_injective⟩

theorem exists_regularEuler_combination_cdtHolonomy (a b c : ℚ)
    (P : Fin 14 → ℚ[X]) (D : ℕ) (hP : ∀ i, (P i).natDegree < D) :
    ∃ R : Fin 14 → ℚ[X], (∀ i, (R i).natDegree < D + 3) ∧
      (PowerSeries.X : PowerSeries ℚ) ^ 3 *
          ∑ i, (P i : PowerSeries ℚ) * cdtHolonomySeries a b c i =
        ∑ i, (R i : PowerSeries ℚ) *
          holonomyRegularEulerSeries (symmetrizedDescent (a • hA + b • hB + c • hC)) i := by
  let e := cdtHolonomyOrderEquiv
  let Q : Fin 14 → ℚ[X] := fun i => P (e.symm i)
  have hQ (i : Fin 14) : (Q i).natDegree < D := hP (e.symm i)
  refine ⟨holonomyRegularEulerPolynomials Q,
    holonomyRegularEulerPolynomials_natDegree_lt Q D hQ, ?_⟩
  have hs : ∑ i, (P i : PowerSeries ℚ) * cdtHolonomySeries a b c i =
      ∑ i, (Q i : PowerSeries ℚ) * cdtFourteenSeries a b c i := by
    apply Fintype.sum_equiv e
    intro i
    simp only [Q, Equiv.symm_apply_apply]
    rfl
  rw [hs, holonomyRegularEuler_combination_eq]

end DirichletL

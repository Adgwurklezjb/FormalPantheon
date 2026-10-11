import Analysis.AuxiliaryFormalSeries
import Analysis.AuxiliaryIntegerKernel
import Analysis.HolonomyFormalIndependence

/-!
Nonzero auxiliary formal series for the actual fourteen CDT functions,
supplied v2 TeX 3965-3998 and 8280-8331. The integer matrix and its
uniform entry bound remain explicit inputs to the kernel application.
-/

namespace DirichletL

open Filter
open scoped Classical Topology

theorem eq_zero_of_cdtHolonomySeriesPolynomialRelation (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) (P : Fin 14 → Polynomial ℚ)
    (hP : ∑ i, (P i : PowerSeries ℚ) * cdtHolonomySeries a b c i = 0) : P = 0 := by
  let e : Fin 14 ≃ Fin 14 := Equiv.ofBijective cdtHolonomyOrder
    ⟨cdtHolonomyOrder_injective, by decide⟩
  let Q : Fin 14 → Polynomial ℚ := fun i => P (e.symm i)
  have hQ : ∑ i, (Q i : PowerSeries ℚ) * cdtFourteenSeries a b c i = 0 := by
    rw [← e.sum_comp]
    simpa only [Q, Equiv.symm_apply_apply, cdtHolonomySeries, Function.comp_def] using hP
  have hz := eq_zero_of_cdtFourteenSeriesPolynomialRelation a b c hrel hne Q hQ
  funext i
  simpa only [Q, Equiv.symm_apply_apply, Pi.zero_apply] using congrFun hz (e i)

theorem cdtAuxiliaryFormalSeries_ne_zero (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) (h D : ℕ) (ε : ℝ)
    (t : ↥(auxiliaryFreeIndices 14 h D ε) → ℤ) (ht : t ≠ 0) :
    auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε t ≠ 0 :=
  auxiliaryFormalSeries_ne_zero (cdtHolonomySeries a b c)
    (eq_zero_of_cdtHolonomySeriesPolynomialRelation a b c hrel hne) h D ε t ht

theorem exists_cdtAuxiliaryFormalSeries_small_kernel (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ δ < 14 ∧ ∀ K : ℝ, 0 ≤ K → ∀ ζ : ℝ, 0 < ζ →
      ∀ᶠ h : ℕ in atTop, ∀ᶠ D : ℕ in atTop, ∀ L : ℕ,
        (14 + δ) * D ≤ L → (L : ℝ) ≤ (14 + δ) * D + 1 →
        ∀ A : Matrix ↥(auxiliaryConstraintIndices (14 * h) L
          ((14 + δ) * D) ((14 - δ) * D) ε) ↥(auxiliaryFreeIndices 14 h D ε) ℤ,
          (∀ i j, |(A i j : ℝ)| ≤ Real.exp (K * (14 * h : ℕ) * D)) →
          ∃ t : ↥(auxiliaryFreeIndices 14 h D ε) → ℤ, t ≠ 0 ∧ A.mulVec t = 0 ∧
            (∀ j, |(t j : ℝ)| ≤ Real.exp (ζ * (14 * h : ℕ) * D)) ∧
            auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε t ≠ 0 := by
  obtain ⟨δ, hδ, hδε, hδm, hker⟩ := exists_auxiliary_integer_kernel (m := 14) (by decide) hε
  refine ⟨δ, hδ, hδε, hδm, fun K hK ζ hζ => ?_⟩
  filter_upwards [hker K hK ζ hζ] with h hh
  filter_upwards [hh] with D hD
  intro L hRL hLR A hA
  obtain ⟨t, ht, hAt, hsize⟩ := hD L hRL hLR A hA
  exact ⟨t, ht, hAt, hsize, cdtAuxiliaryFormalSeries_ne_zero a b c hrel hne h D ε t ht⟩

end DirichletL

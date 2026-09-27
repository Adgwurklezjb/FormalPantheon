import Analysis.AuxiliaryCoefficientBounds
import Analysis.HolonomyConstructionDenominators
import Analysis.PowerSeriesCoefficientBounds
import Analysis.HolonomyAuxiliarySeries

/-!
The actual integer matrix and finite coefficient vanishing in CDT v2,
supplied TeX 3965-3998 and 8280-8331. The zero estimate is separate.
-/

namespace DirichletL

open Filter
open scoped Classical

theorem exists_cdtAuxiliaryCoefficientMatrix_bound (a b c : ℤ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h D L : ℕ, 0 < D → (L : ℝ) ≤ (14 + δ) * D + 1 →
      ∀ R S ε : ℝ, ∃ A : Matrix ↥(auxiliaryConstraintIndices (14 * h) L R S ε)
          ↥(auxiliaryFreeIndices 14 h D ε) ℤ,
        (∀ n p, |(A n p : ℝ)| ≤ Real.exp (K * (14 * h : ℕ) * D)) ∧
        ∀ t : ↥(auxiliaryFreeIndices 14 h D ε) → ℤ, A.mulVec t = 0 ↔
          ∀ n : ↥(auxiliaryConstraintIndices (14 * h) L R S ε),
            MvPowerSeries.coeff (R := ℚ) (Finsupp.equivFunOnFinite.symm (fun j => (n.val j).val))
              (auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε t) = 0 := by
  obtain ⟨C, hC, hf⟩ := exists_uniform_coeff_bound_of_radius_pos
    (cdtHolonomySeries a b c)
    (fun i => (hasFPowerSeriesAt_cdtHolonomyFamily a b c (by exact_mod_cast hrel) i).radius_pos)
  obtain ⟨M, hM, hclear⟩ := exists_common_clearing_cdtHolonomySeries a b c
  have hMabs : (1 : ℝ) ≤ |(M : ℝ)| := by
    have hpos : (0 : ℤ) < |M| := abs_pos.mpr hM
    have hone : (1 : ℤ) ≤ |M| := by omega
    exact_mod_cast hone
  obtain ⟨K, hK, hsize⟩ := exists_auxiliary_clearing_height_rate hMabs hC
    (show (0 : ℝ) ≤ 14 + δ by linarith)
  refine ⟨K, hK, fun h D L hD hL R S ε => ?_⟩
  let P : ℤ := M * (lcmPrefix (2 * L + 6) : ℤ) ^ 3
  have hP : P ≠ 0 := mul_ne_zero hM
    (pow_ne_zero _ (by exact_mod_cast (lcmPrefix_pos (2 * L + 6)).ne'))
  have hfp (i : Fin 14) (n : ℕ) (hn : n ≤ L) : IsLocalization.IsInteger ℤ
      ((P : ℚ) * PowerSeries.coeff (R := ℚ) n (cdtHolonomySeries a b c i)) := by
    simpa only [P, Int.cast_mul, Int.cast_pow, Int.cast_natCast] using hclear L i n hn
  obtain ⟨A, hA, hkernel⟩ := exists_integer_auxiliaryCoefficientMatrix
    (cdtHolonomySeries a b c) h D L R S ε P hP hfp
  have hA' : ∀ n p, (A n p : ℚ) =
      ((M : ℚ) * (lcmPrefix (2 * L + 6) : ℚ) ^ 3) ^ (14 * h) *
        auxiliaryCoefficientMatrix (cdtHolonomySeries a b c) h D L R S ε n p := by
    simpa only [P, Int.cast_mul, Int.cast_pow, Int.cast_natCast] using hA
  refine ⟨A, fun n p => ?_, hkernel⟩
  exact (abs_cleared_auxiliaryCoefficientMatrix_le
    (cdtHolonomySeries a b c) h D L R S ε hC hf M A hA' n p).trans
      (hsize (14 * h) D L hD hL)

theorem exists_cdtAuxiliaryFormalSeries_small_vanishing (a b c : ℤ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ δ < 14 ∧ ∀ ζ : ℝ, 0 < ζ →
      ∀ᶠ h : ℕ in atTop, ∀ᶠ D : ℕ in atTop, ∀ L : ℕ,
        (14 + δ) * D ≤ L → (L : ℝ) ≤ (14 + δ) * D + 1 →
        ∃ t : ↥(auxiliaryFreeIndices 14 h D ε) → ℤ, t ≠ 0 ∧
          (∀ p, |(t p : ℝ)| ≤ Real.exp (ζ * (14 * h : ℕ) * D)) ∧
          auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε t ≠ 0 ∧
          ∀ n : ↥(auxiliaryConstraintIndices (14 * h) L
              ((14 + δ) * D) ((14 - δ) * D) ε),
            MvPowerSeries.coeff (R := ℚ) (Finsupp.equivFunOnFinite.symm (fun j => (n.val j).val))
              (auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε t) = 0 := by
  obtain ⟨δ, hδ, hδε, hδm, hker⟩ := exists_cdtAuxiliaryFormalSeries_small_kernel a b c
    (by exact_mod_cast hrel) (by exact_mod_cast hne) hε
  obtain ⟨K, hK, hmat⟩ := exists_cdtAuxiliaryCoefficientMatrix_bound a b c hrel hδ.le
  refine ⟨δ, hδ, hδε, hδm, fun ζ hζ => ?_⟩
  filter_upwards [hker K hK ζ hζ] with h hh
  filter_upwards [hh, eventually_ge_atTop 1] with D hkernelD hDone
  intro L hRL hLR
  obtain ⟨A, hbound, hzero⟩ := hmat h D L (by omega) hLR
    ((14 + δ) * D) ((14 - δ) * D) ε
  obtain ⟨t, ht, hAt, hsize, hF⟩ := hkernelD L hRL hLR A hbound
  exact ⟨t, ht, hsize, hF, (hzero t).mp hAt⟩

end DirichletL

import Analysis.AuxiliaryFormalSeries

/-!
The literal rational and integer coefficient matrices in CDT v2,
supplied TeX 3965-3998. Rows are restricted to the explicit finite cube.
-/

noncomputable section

namespace DirichletL

open scoped Classical

/-- Coefficients of the literal auxiliary monomials at the constrained exponents. -/
def auxiliaryCoefficientMatrix {m : ℕ} (f : Fin m → PowerSeries ℚ)
    (h D L : ℕ) (R S ε : ℝ) :
    Matrix ↥(auxiliaryConstraintIndices (m * h) L R S ε)
      ↥(auxiliaryFreeIndices m h D ε) ℚ := fun n p =>
  MvPowerSeries.coeff (R := ℚ) (Finsupp.equivFunOnFinite.symm (fun j => (n.val j).val))
    (auxiliarySeriesTerm f p.val)

theorem auxiliaryCoefficientMatrix_apply {m : ℕ} (f : Fin m → PowerSeries ℚ)
    (h D L : ℕ) (R S ε : ℝ)
    (n : ↥(auxiliaryConstraintIndices (m * h) L R S ε))
    (p : ↥(auxiliaryFreeIndices m h D ε)) :
    auxiliaryCoefficientMatrix f h D L R S ε n p =
      if ∀ j, (p.val.2 j).val ≤ (n.val j).val then
        ∏ j, PowerSeries.coeff (R := ℚ) ((n.val j).val - (p.val.2 j).val) (f (p.val.1 j))
      else 0 := by
  simp [auxiliaryCoefficientMatrix, coeff_auxiliarySeriesTerm]

theorem auxiliaryCoefficientMatrix_mulVec {m : ℕ} (f : Fin m → PowerSeries ℚ)
    (h D L : ℕ) (R S ε : ℝ) (t : ↥(auxiliaryFreeIndices m h D ε) → ℤ)
    (n : ↥(auxiliaryConstraintIndices (m * h) L R S ε)) :
    (auxiliaryCoefficientMatrix f h D L R S ε).mulVec (fun p => (t p : ℚ)) n =
      MvPowerSeries.coeff (R := ℚ) (Finsupp.equivFunOnFinite.symm (fun j => (n.val j).val))
        (auxiliaryFormalSeries f h D ε t) := by
  simp only [auxiliaryCoefficientMatrix, Matrix.mulVec, dotProduct,
    auxiliaryFormalSeries, map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl (fun p _ => mul_comm _ _)

theorem isInteger_auxiliaryCoefficientMatrix {m : ℕ} (f : Fin m → PowerSeries ℚ)
    (h D L : ℕ) (R S ε : ℝ) (M : ℤ)
    (hf : ∀ i n, n ≤ L → IsLocalization.IsInteger ℤ ((M : ℚ) * PowerSeries.coeff (R := ℚ) n (f i)))
    (n : ↥(auxiliaryConstraintIndices (m * h) L R S ε))
    (p : ↥(auxiliaryFreeIndices m h D ε)) :
    IsLocalization.IsInteger ℤ
      ((M : ℚ) ^ (m * h) * auxiliaryCoefficientMatrix f h D L R S ε n p) := by
  rw [auxiliaryCoefficientMatrix_apply]
  split_ifs
  · have hp := (algebraMap ℤ ℚ).rangeS.prod_mem
      (t := Finset.univ)
      (f := fun j : Fin (m * h) => (M : ℚ) *
        PowerSeries.coeff (R := ℚ) ((n.val j).val - (p.val.2 j).val) (f (p.val.1 j)))
      (fun j _ => hf _ _ ((Nat.sub_le _ _).trans (Nat.le_of_lt (n.val j).isLt)))
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] using hp
  · simpa only [mul_zero] using (IsLocalization.isInteger_zero (R := ℤ) (S := ℚ))

theorem exists_integer_auxiliaryCoefficientMatrix {m : ℕ} (f : Fin m → PowerSeries ℚ)
    (h D L : ℕ) (R S ε : ℝ) (M : ℤ) (hM : M ≠ 0)
    (hf : ∀ i n, n ≤ L → IsLocalization.IsInteger ℤ ((M : ℚ) * PowerSeries.coeff (R := ℚ) n (f i))) :
    ∃ A : Matrix ↥(auxiliaryConstraintIndices (m * h) L R S ε)
        ↥(auxiliaryFreeIndices m h D ε) ℤ,
      (∀ n p, (A n p : ℚ) =
        (M : ℚ) ^ (m * h) * auxiliaryCoefficientMatrix f h D L R S ε n p) ∧
      ∀ t : ↥(auxiliaryFreeIndices m h D ε) → ℤ, A.mulVec t = 0 ↔
        ∀ n : ↥(auxiliaryConstraintIndices (m * h) L R S ε),
          MvPowerSeries.coeff (R := ℚ) (Finsupp.equivFunOnFinite.symm (fun j => (n.val j).val))
            (auxiliaryFormalSeries f h D ε t) = 0 := by
  have hentry : ∀ n p, ∃ z : ℤ, (z : ℚ) =
      (M : ℚ) ^ (m * h) * auxiliaryCoefficientMatrix f h D L R S ε n p :=
    fun n p => isInteger_auxiliaryCoefficientMatrix f h D L R S ε M hf n p
  choose A hA using hentry
  change Matrix ↥(auxiliaryConstraintIndices (m * h) L R S ε)
    ↥(auxiliaryFreeIndices m h D ε) ℤ at A
  refine ⟨A, hA, fun t => ?_⟩
  have hrow (n : ↥(auxiliaryConstraintIndices (m * h) L R S ε)) :
      ((Matrix.mulVec A t n : ℤ) : ℚ) = (M : ℚ) ^ (m * h) *
        MvPowerSeries.coeff (R := ℚ) (Finsupp.equivFunOnFinite.symm (fun j => (n.val j).val))
          (auxiliaryFormalSeries f h D ε t) := by
    calc
      ((Matrix.mulVec A t n : ℤ) : ℚ) = ∑ p, (A n p : ℚ) * (t p : ℚ) := by
        simp [Matrix.mulVec, dotProduct]
      _ = (M : ℚ) ^ (m * h) *
          (auxiliaryCoefficientMatrix f h D L R S ε).mulVec (fun p => (t p : ℚ)) n := by
        simp only [Matrix.mulVec, dotProduct, hA, Finset.mul_sum, mul_assoc]
      _ = _ := by rw [auxiliaryCoefficientMatrix_mulVec]
  have hM' : (M : ℚ) ^ (m * h) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hM)
  constructor
  · intro ht n
    have hz : (M : ℚ) ^ (m * h) *
        MvPowerSeries.coeff (R := ℚ) (Finsupp.equivFunOnFinite.symm (fun j => (n.val j).val))
          (auxiliaryFormalSeries f h D ε t) = 0 := by
      rw [← hrow n, ht]
      simp
    exact (mul_eq_zero.mp hz).resolve_left hM'
  · intro ht
    funext n
    have hz : ((Matrix.mulVec A t n : ℤ) : ℚ) = 0 := by rw [hrow n, ht n, mul_zero]
    exact_mod_cast hz

end DirichletL

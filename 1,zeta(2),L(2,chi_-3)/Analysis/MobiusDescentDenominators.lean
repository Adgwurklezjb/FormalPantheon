import Analysis.MobiusDescent
import Arithmetic.IntegerDenominators

/-!
Single-multiplier coefficient clearing through integral substitution and
Mobius descent, for CDT v2, Lemmas `etalecover` and `bdenominators`
(supplied TeX 7443-7465). The descent recursion has unit diagonal (-1)^n.
-/

namespace DirichletL

theorem isInteger_lcmPrefix_mul_coeff_mul_map_int {f : PowerSeries ℚ}
    (hf : ∀ n, IsLocalization.IsInteger ℤ
      ((lcmPrefix n : ℚ) * PowerSeries.coeff (R := ℚ) n f)) (g : PowerSeries ℤ) (n : ℕ) :
    IsLocalization.IsInteger ℤ ((lcmPrefix n : ℚ) *
      PowerSeries.coeff (R := ℚ) n (f * PowerSeries.map (Int.castRingHom ℚ) g)) := by
  rw [PowerSeries.coeff_mul]
  apply isInteger_nat_mul_sum
  intro p hp
  rw [PowerSeries.coeff_map]
  exact isInteger_nat_mul_mul_int
    (isInteger_nat_mul_of_dvd (hf p.1)
      (lcmPrefix_dvd (Finset.antidiagonal.fst_le hp))) _

theorem isInteger_lcmPrefix_mul_coeff_subst_map_int {f : PowerSeries ℚ}
    (hf : ∀ n, IsLocalization.IsInteger ℤ
      ((lcmPrefix n : ℚ) * PowerSeries.coeff (R := ℚ) n f))
    (g : PowerSeries ℤ) (hg : PowerSeries.constantCoeff (R := ℤ) g = 0) (n : ℕ) :
    IsLocalization.IsInteger ℤ ((lcmPrefix n : ℚ) * PowerSeries.coeff (R := ℚ) n
      (MvPowerSeries.subst (fun (_ : Unit) => PowerSeries.map (Int.castRingHom ℚ) g) f)) := by
  have hgq : PowerSeries.constantCoeff (R := ℚ) (PowerSeries.map (Int.castRingHom ℚ) g) = 0 := by
    change (PowerSeries.constantCoeff (R := ℤ) g : ℚ) = 0
    rw [hg, Int.cast_zero]
  rw [coeff_subst_eq_sum f _ hgq]
  apply isInteger_nat_mul_sum
  intro k hk
  rw [← map_pow, PowerSeries.coeff_map]
  exact isInteger_nat_mul_mul_int
    (isInteger_nat_mul_of_dvd (hf k)
      (lcmPrefix_dvd (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))) _

theorem isInteger_mobiusDescent_of_dvd (f : PowerSeries ℚ) (D : ℕ → ℕ)
    (hD : ∀ k n : ℕ, k ≤ n → D k ∣ D n)
    (hf : ∀ n, IsLocalization.IsInteger ℤ
      ((D n : ℚ) * PowerSeries.coeff (R := ℚ) (2 * n) f)) (n : ℕ) :
    IsLocalization.IsInteger ℤ
      ((D n : ℚ) * PowerSeries.coeff (R := ℚ) n (mobiusDescent f)) := by
  simp only [coeff_mobiusDescent]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [mobiusDescentCoeff_eq]
    have hsum : IsLocalization.IsInteger ℤ ((D n : ℚ) *
        ∑ k ∈ Finset.range n, mobiusDescentCoeff f k *
          PowerSeries.coeff (R := ℚ) (2 * n) (mobiusCoordinateQ ^ k)) := by
      apply isInteger_nat_mul_sum
      intro k hk
      have hy : mobiusCoordinateQ =
          PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.X + mobiusInvolution) := by
        simp [mobiusCoordinateQ, mobiusInvolutionQ]
      rw [hy, ← map_pow, PowerSeries.coeff_map]
      exact isInteger_nat_mul_mul_int
        (isInteger_nat_mul_of_dvd (ih k (Finset.mem_range.mp hk))
          (hD k n (Nat.le_of_lt (Finset.mem_range.mp hk)))) _
    have hdiff := isInteger_nat_mul_sub (hf n) hsum
    simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one, mul_comm] using
      isInteger_nat_mul_mul_int hdiff ((-1 : ℤ) ^ n)

theorem isInteger_lcmPrefix_mul_coeff_symmetrizedDescent {f : PowerSeries ℚ}
    (hf : ∀ n, IsLocalization.IsInteger ℤ
      ((lcmPrefix n : ℚ) * PowerSeries.coeff (R := ℚ) n f)) (n : ℕ) :
    IsLocalization.IsInteger ℤ ((lcmPrefix (2 * n) : ℚ) *
      PowerSeries.coeff (R := ℚ) n (symmetrizedDescent f)) := by
  apply isInteger_mobiusDescent_of_dvd (symmetrizedFormal f)
    (fun k => lcmPrefix (2 * k))
  · intro k m hkm
    exact lcmPrefix_dvd (Nat.mul_le_mul_left 2 hkm)
  · intro k
    simpa only [symmetrizedFormal, map_add, mul_add] using
      IsLocalization.isInteger_add (hf (2 * k))
        (isInteger_lcmPrefix_mul_coeff_subst_map_int hf mobiusInvolution
          constantCoeff_mobiusInvolution (2 * k))

end DirichletL

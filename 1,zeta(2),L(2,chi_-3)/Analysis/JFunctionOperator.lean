import Analysis.JFunction

/-!
The formal second-order LL equation following CDT v2, `newfunction`
(supplied TeX lines 7374-7387). Coefficient uniqueness includes the
singular initial point and uses exact rational arithmetic.
-/

namespace DirichletL

local notation "D" => PowerSeries.derivative ℚ
local notation "x" => (PowerSeries.X : PowerSeries ℚ)

/-- The source's second-order operator LL on rational formal series. -/
noncomputable def pureJOperator (f : PowerSeries ℚ) : PowerSeries ℚ :=
  2 * x * (1 - x) ^ 2 * D (D f) + (2 - x) * (1 - x) * D f + f

private theorem pureJOperator_expanded (f : PowerSeries ℚ) :
    pureJOperator f =
      PowerSeries.C (R := ℚ) 2 * (x ^ 1 * D (D f)) -
      PowerSeries.C (R := ℚ) 4 * (x ^ 2 * D (D f)) +
      PowerSeries.C (R := ℚ) 2 * (x ^ 3 * D (D f)) +
      PowerSeries.C (R := ℚ) 2 * D f - PowerSeries.C (R := ℚ) 3 * (x ^ 1 * D f) +
      x ^ 2 * D f + f := by
  simp only [pureJOperator, map_ofNat]
  ring

theorem coeff_pureJOperator (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n (pureJOperator f) =
      if n = 0 then 2 * PowerSeries.coeff (R := ℚ) 1 f + PowerSeries.coeff (R := ℚ) 0 f else
        2 * ((n : ℚ) + 1) ^ 2 * PowerSeries.coeff (R := ℚ) (n + 1) f +
          (-4 * (n : ℚ) ^ 2 + n + 1) * PowerSeries.coeff (R := ℚ) n f +
          ((n : ℚ) - 1) * (2 * n - 3) * PowerSeries.coeff (R := ℚ) (n - 1) f := by
  rw [pureJOperator_expanded]
  by_cases hn : n = 0
  · subst n
    have hd : PowerSeries.constantCoeff (R := ℚ) (D f) = PowerSeries.coeff (R := ℚ) 1 f := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
      norm_num
    simp [PowerSeries.coeff_derivative, PowerSeries.coeff_X_pow_mul', hd]
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_derivative, if_neg hn]
  by_cases hn3 : 3 ≤ n
  · have hn2 : 2 ≤ n := by omega
    simp only [if_pos hn1, if_pos hn2, if_pos hn3]
    rw [show n - 1 + 1 = n by omega,
      show n - 2 + 1 + 1 = n by omega,
      show n - 3 + 1 + 1 = n - 1 by omega,
      show n - 2 + 1 = n - 1 by omega]
    push_cast [Nat.cast_sub (R := ℚ) hn1,
      Nat.cast_sub (R := ℚ) hn2, Nat.cast_sub (R := ℚ) hn3]
    ring
  · interval_cases n <;> norm_num at * <;> ring

/-- The singular LL equation has at most one series with a given constant term. -/
theorem pureJOperator_injective_of_constantCoeff {f g : PowerSeries ℚ}
    (hode : pureJOperator f = pureJOperator g)
    (h0 : PowerSeries.constantCoeff (R := ℚ) f = PowerSeries.constantCoeff (R := ℚ) g) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h0
    have he := congrArg (PowerSeries.coeff (R := ℚ) n) hode
    rw [coeff_pureJOperator, coeff_pureJOperator] at he
    have hn : PowerSeries.coeff (R := ℚ) n f = PowerSeries.coeff (R := ℚ) n g := ih n (by omega)
    by_cases hn0 : n = 0
    · subst n
      simp [hn] at he
      linarith
    · have hp := ih (n - 1) (by omega : n - 1 < n + 1)
      simp only [if_neg hn0, hn, hp] at he
      have he' : 2 * ((n : ℚ) + 1) ^ 2 * PowerSeries.coeff (R := ℚ) (n + 1) f =
          2 * ((n : ℚ) + 1) ^ 2 * PowerSeries.coeff (R := ℚ) (n + 1) g := by
        linarith
      exact mul_left_cancel₀ (by positivity : (2 : ℚ) * ((n : ℚ) + 1) ^ 2 ≠ 0) he'

private theorem shifted_logarithm_derivative :
    (1 - x) * (formalShift pureLogarithmSeries + x * D (formalShift pureLogarithmSeries)) =
      1 := by
  have he : formalShift pureLogarithmSeries + x * D (formalShift pureLogarithmSeries) =
      D pureLogarithmSeries := by
    have h := congrArg D (X_mul_formalShift_of_constantCoeff_zero
      (f := pureLogarithmSeries) (by simp [pureLogarithmSeries]))
    simpa only [Derivation.leibniz, PowerSeries.derivative_X, smul_eq_mul, mul_one,
      add_comm] using h
  rw [he]
  ext n
  cases n with
  | zero =>
    simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_zero_X_mul,
      PowerSeries.coeff_derivative, coeff_pureLogarithmSeries]
    norm_num
  | succ n =>
    simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_derivative, coeff_pureLogarithmSeries, PowerSeries.coeff_one,
      if_neg (Nat.succ_ne_zero n)]
    push_cast
    field_simp
    ring

private theorem derivative_ofNat (n : ℕ) [n.AtLeastTwo] :
    D (ofNat(n) : PowerSeries ℚ) = 0 :=
  (PowerSeries.derivative ℚ).map_natCast n

theorem pureJOperator_pureJSeries : pureJOperator pureJSeries = 2 * (1 - x) := by
  let b := formalShift pureLogarithmSeries
  have h0 : 2 * (x - 1) * D pureJSeries - pureJSeries - 2 * (x - 1) * b = 0 := by
    have h := pureJSeries_ode
    simp only [map_ofNat] at h
    change 2 * (x - 1) * pureJSeries.derivativeFun - pureJSeries -
      2 * (x - 1) * b = 0
    linear_combination h
  have h1 := congrArg D h0
  simp only [map_sub, map_zero, Derivation.leibniz, derivative_ofNat,
    Derivation.map_one_eq_zero, PowerSeries.derivative_X, smul_eq_mul,
    sub_zero, mul_zero, zero_mul, zero_add, one_mul] at h1
  have hb : (1 - x) * (b + x * D b) = 1 := shifted_logarithm_derivative
  dsimp only [pureJOperator]
  linear_combination x * (x - 1) * h1 - h0 - 2 * (x - 1) * hb

end DirichletL

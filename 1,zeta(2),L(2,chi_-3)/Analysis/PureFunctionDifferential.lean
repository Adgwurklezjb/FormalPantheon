import Analysis.PureFunctionPullback
import Analysis.JFunctionFactorial

/-!
The formal differential system in CDT v2, equation `diffformulas`
(supplied TeX lines 7975-7982). The B4 equation follows from its
Möbius pullback; the B5 equation uses exact factorial coefficients.
-/

namespace DirichletL

local notation "D" => PowerSeries.derivative ℚ
local notation "x" => (PowerSeries.X : PowerSeries ℚ)
local notation "w" => mobiusInvolutionQ
local notation "y" => mobiusCoordinateQ
local notation "u" => (1 - mobiusInvolutionQ)
local notation "δ" => (x - mobiusInvolutionQ)
local notation "A" => pureLogarithmSeries
local notation "L" => pureDilogarithmSeries
local notation "H" => (L - MvPowerSeries.subst (fun (_ : Unit) => w) L)

theorem pureB3Series_first_order_ode :
    x * (4 - x) * D pureB3Series = -pureB2Series + 2 * x := by
  simp only [pureB2Series, map_ofNat]
  ring

private theorem derivative_pureDilogarithm_difference_scaled :
    (x - 1) * δ * D H = (y - 4) * A := by
  have ht : 2 * H = 4 * L + A ^ 2 := by
    have h := two_mul_symmetrizedFormal_pureDilogarithmSeries
    change 2 * (L + MvPowerSeries.subst (fun (_ : Unit) => w) L) = -A ^ 2 at h
    linear_combination -h
  have hd : 2 * D H = 4 * D L + 2 * A * u := by
    have h := congrArg D ht
    have h2 : D (2 : PowerSeries ℚ) = 0 := (PowerSeries.derivative ℚ).map_natCast 2
    have h4 : D (4 : PowerSeries ℚ) = 0 := (PowerSeries.derivative ℚ).map_natCast 4
    simp only [Derivation.leibniz, h2, h4, smul_eq_mul, mul_zero,
      add_zero, map_add, Derivation.leibniz_pow, derivative_pureLogarithmSeries,
      nsmul_eq_mul] at h
    norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_one] at h
    linear_combination h
  have hδ : (x - 1) * δ = x * (x - 2) := by
    linear_combination -X_sub_one_mul_mobiusInvolutionQ
  have hu : (x - 1) * u = -1 := by
    linear_combination -one_sub_X_mul_one_sub_mobiusInvolutionQ
  apply mul_left_cancel₀ (show (2 : PowerSeries ℚ) ≠ 0 by
    intro h
    have hc := congrArg (PowerSeries.constantCoeff (R := ℚ)) h
    norm_num [map_ofNat] at hc)
  calc
    _ = ((x - 1) * δ) * (2 * D H) := by ring
    _ = ((x - 1) * δ) * (4 * D L + 2 * A * u) := by rw [hd]
    _ = 4 * (x - 2) * (x * D L) + 2 * δ * A * ((x - 1) * u) := by
      linear_combination (4 * D L) * hδ
    _ = 4 * (x - 2) * A - 2 * δ * A := by
      rw [X_mul_derivative_pureDilogarithmSeries, hu]
      ring
    _ = _ := by
      dsimp only [mobiusCoordinateQ]
      ring

theorem pureB4Series_ode :
    x * (4 - x) * D pureB4Series =
      (2 - x) * pureB4Series + (4 - x) * pureB2Series - 2 * x * (4 - x) := by
  have hy : MvPowerSeries.HasSubst (fun (_ : Unit) => y) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusCoordinateQ)
  let s : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ := MvPowerSeries.substAlgHom hy
  have hs (f : PowerSeries ℚ) : s f = MvPowerSeries.subst (fun (_ : Unit) => y) f :=
    MvPowerSeries.substAlgHom_apply hy f
  have hsx : s x = y := MvPowerSeries.substAlgHom_X hy ()
  have hb : s pureB4Series = δ * H := (hs _).trans subst_pureB4Series
  have h2 : s pureB2Series = 2 * y + δ * A := (hs _).trans subst_pureB2Series
  have hd : D (s pureB4Series) = s (D pureB4Series) * D y := by
    rw [hs, hs]
    exact derivativeFun_subst pureB4Series y constantCoeff_mobiusCoordinateQ
  have hc : δ * s (D pureB4Series) = (x - 1) * D (s pureB4Series) := by
    rw [hd]
    linear_combination -s (D pureB4Series) * X_sub_one_mul_derivative_coordinate
  have he : δ * s (D pureB4Series) = (y - 2) * H + (y - 4) * A := by
    rw [hc, hb]
    simp only [Derivation.leibniz, smul_eq_mul]
    linear_combination H * X_sub_one_mul_derivative_difference +
      derivative_pureDilogarithm_difference_scaled
  apply subst_mobiusCoordinateQ_injective
  rw [← hs, ← hs]
  simp only [map_mul, map_sub, map_add, map_ofNat, hsx, h2]
  calc
    _ = -δ ^ 2 * s (D pureB4Series) := by rw [mobius_difference_sq]; ring
    _ = -δ * ((y - 2) * H + (y - 4) * A) := by rw [← he]; ring
    _ = (2 - y) * (δ * H) + (4 - y) * δ * A := by ring
    _ = _ := by rw [← hb]; ring

private theorem pureB5_B2_coefficient_relation (n : ℕ) :
    4 * (2 * (n : ℚ) + 3) * pureB5QuotientCoeff (n + 1) -
      (2 * n + 1) * pureB5QuotientCoeff n +
      2 * PowerSeries.coeff (R := ℚ) (n + 2) pureB2Series = 0 := by
  rw [pureB5QuotientCoeff_succ, coeff_pureB2Series_add_two_ratio]
  dsimp only [pureB5QuotientCoeff, pureB3QuotientCoeff]
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, Nat.factorial_succ (2 * n + 1)]
  push_cast
  field_simp
  ring

theorem pureB5Series_first_order_ode :
    2 * x * (4 - x) * D pureB5Series =
      (4 - x) * pureB5Series - 2 * pureB2Series + 4 * x := by
  have he : 2 * x * (4 - x) * D pureB5Series -
      ((4 - x) * pureB5Series - 2 * pureB2Series + 4 * x) =
      PowerSeries.C (R := ℚ) 8 * (x * D pureB5Series) -
        PowerSeries.C (R := ℚ) 2 * (x * (x * D pureB5Series)) -
        PowerSeries.C (R := ℚ) 4 * pureB5Series + x * pureB5Series +
        PowerSeries.C (R := ℚ) 2 * pureB2Series - PowerSeries.C (R := ℚ) 4 * x := by
    simp only [map_ofNat]
    ring
  apply sub_eq_zero.mp
  rw [he]
  ext n
  rcases n with _ | (_ | n)
  · simp
  · change PowerSeries.coeff (R := ℚ) (0 + 1) _ = PowerSeries.coeff (R := ℚ) (0 + 1) 0
    simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_derivative,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_pureB5Series,
      coeff_one_pureB2Series, map_zero, PowerSeries.coeff_X]
    norm_num [coeff_pureB5Series_succ]
  · simp only [map_sub, map_add, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
      map_zero, PowerSeries.coeff_X,
      if_neg (by omega : ¬n + 1 + 1 = 1)]
    change 8 * (PowerSeries.coeff (R := ℚ) (n + 2) pureB5Series * (↑(n + 1) + 1)) -
      2 * (PowerSeries.coeff (R := ℚ) (n + 1) pureB5Series * (↑n + 1)) -
      4 * PowerSeries.coeff (R := ℚ) (n + 2) pureB5Series +
      PowerSeries.coeff (R := ℚ) (n + 1) pureB5Series +
      2 * PowerSeries.coeff (R := ℚ) (n + 2) pureB2Series - 4 * 0 = 0
    have hcoeff (k : ℕ) : PowerSeries.coeff (R := ℚ) (k + 1) pureB5Series =
        pureB5QuotientCoeff k := by
      rw [pureB5Series, PowerSeries.coeff_succ_X_mul, coeff_pureB5QuotientSeries]
    rw [show n + 2 = (n + 1) + 1 by omega, hcoeff, hcoeff]
    push_cast
    linear_combination pureB5_B2_coefficient_relation n

end DirichletL

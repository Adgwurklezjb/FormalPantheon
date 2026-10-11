import Analysis.PureFunctionInvolution
import Analysis.PureFunctionFactorial

/-!
The B2, B3, and B4 descents in CDT v2, `defB` and `diffformulas`
(supplied TeX lines 7327-7348 and 7975-7982). The operator comparison
uses only unit cancellation and the existing formal substitution chain rule.
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

private theorem X_sub_one_ne_zero : x - 1 ≠ 0 := by
  intro h
  have hc := congrArg (PowerSeries.constantCoeff (R := ℚ)) h
  norm_num at hc

theorem X_sub_one_mul_derivative_coordinate : (x - 1) * D y = δ := by
  rw [derivative_mobiusCoordinateQ]
  linear_combination u * one_sub_X_mul_one_sub_mobiusInvolutionQ

theorem X_sub_one_mul_derivative_difference : (x - 1) * D δ = y - 2 := by
  simp only [map_sub, PowerSeries.derivative_X, derivative_mobiusInvolutionQ]
  dsimp only [mobiusCoordinateQ]
  linear_combination -u * one_sub_X_mul_one_sub_mobiusInvolutionQ

theorem mobius_difference_sq : δ ^ 2 = -y * (4 - y) := by
  dsimp only [mobiusCoordinateQ]
  linear_combination -4 * X_sub_one_mul_mobiusInvolutionQ

private theorem constantCoeff_derivative_subst_coordinate (f : PowerSeries ℚ) :
    PowerSeries.constantCoeff (R := ℚ)
      (D (MvPowerSeries.subst (fun (_ : Unit) => y) f)) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative,
    coeff_subst_one constantCoeff_mobiusCoordinateQ, coeff_one_mobiusCoordinateQ]
  simp

/-- The factorial B3 operator becomes a factored logarithmic operator under pullback. -/
theorem pureB3Operator_pullback (f : PowerSeries ℚ) :
    (x - 1) * D ((x - 1) * D (MvPowerSeries.subst (fun (_ : Unit) => y) f)) =
      -MvPowerSeries.subst (fun (_ : Unit) => y) (pureB3Operator f) := by
  have hy : MvPowerSeries.HasSubst (fun (_ : Unit) => y) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusCoordinateQ)
  let s : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ := MvPowerSeries.substAlgHom hy
  have hs (g : PowerSeries ℚ) : s g = MvPowerSeries.subst (fun (_ : Unit) => y) g :=
    MvPowerSeries.substAlgHom_apply hy g
  have hsx : s x = y := MvPowerSeries.substAlgHom_X hy ()
  have hd (g : PowerSeries ℚ) : D (s g) = s (D g) * D y := by
    rw [hs, hs]
    exact derivativeFun_subst g y constantCoeff_mobiusCoordinateQ
  have hfirst (g : PowerSeries ℚ) : (x - 1) * D (s g) = δ * s (D g) := by
    rw [hd]
    calc
      _ = ((x - 1) * D y) * s (D g) := by ring
      _ = _ := by rw [X_sub_one_mul_derivative_coordinate]
  rw [← hs, ← hs, hfirst]
  calc
    _ = ((x - 1) * D δ) * s (D f) + δ * ((x - 1) * D (s (D f))) := by
      simp only [Derivation.leibniz, smul_eq_mul]
      ring
    _ = (y - 2) * s (D f) + δ ^ 2 * s (D (D f)) := by
      rw [X_sub_one_mul_derivative_difference, hfirst]
      ring
    _ = _ := by
      rw [mobius_difference_sq]
      simp only [pureB3Operator, map_add, map_mul, map_sub, map_ofNat, hsx]
      ring

/-- The first integral of the pulled-back B3 equation has its constant fixed at zero. -/
theorem X_sub_one_mul_derivative_subst_pureB3Series :
    (x - 1) * D (MvPowerSeries.subst (fun (_ : Unit) => y) pureB3Series) = A := by
  have hy : MvPowerSeries.HasSubst (fun (_ : Unit) => y) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusCoordinateQ)
  have h1 : MvPowerSeries.subst (fun (_ : Unit) => y) (1 : PowerSeries ℚ) = 1 := by
    rw [← MvPowerSeries.substAlgHom_apply hy, map_one]
  apply PowerSeries.derivative.ext
  · apply mul_left_cancel₀ X_sub_one_ne_zero
    rw [pureB3Operator_pullback, pureB3Series_ode, h1, derivative_pureLogarithmSeries]
    linear_combination one_sub_X_mul_one_sub_mobiusInvolutionQ
  · rw [map_mul, constantCoeff_derivative_subst_coordinate]
    simp [pureLogarithmSeries]

/-- The literal factorial B3 pulls back to minus one half of the squared logarithm. -/
theorem two_mul_subst_pureB3Series :
    2 * MvPowerSeries.subst (fun (_ : Unit) => y) pureB3Series = -A ^ 2 := by
  apply PowerSeries.derivative.ext
  · apply mul_left_cancel₀ X_sub_one_ne_zero
    have ht : D (2 : PowerSeries ℚ) = 0 := (PowerSeries.derivative ℚ).map_natCast 2
    simp only [Derivation.leibniz, ht, smul_eq_mul, zero_mul, add_zero,
      map_neg, Derivation.leibniz_pow, derivative_pureLogarithmSeries, nsmul_eq_mul]
    norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_one]
    linear_combination 2 * X_sub_one_mul_derivative_subst_pureB3Series -
      2 * A * one_sub_X_mul_one_sub_mobiusInvolutionQ
  · have h0 : PowerSeries.constantCoeff (R := ℚ)
        (MvPowerSeries.subst (fun (_ : Unit) => y) pureB3Series) = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        coeff_subst_zero constantCoeff_mobiusCoordinateQ]
      simp
    simp [h0, pureLogarithmSeries]

theorem symmetrizedDescent_pureDilogarithmSeries :
    symmetrizedDescent L = pureB3Series := by
  apply subst_mobiusCoordinateQ_injective
  apply mul_left_cancel₀ (show (2 : PowerSeries ℚ) ≠ 0 by
    intro h
    have hc := congrArg (PowerSeries.constantCoeff (R := ℚ)) h
    norm_num [map_ofNat] at hc)
  rw [subst_symmetrizedDescent, two_mul_symmetrizedFormal_pureDilogarithmSeries,
    two_mul_subst_pureB3Series]

theorem symmetrizedDescent_pureLogarithmSeries : symmetrizedDescent A = 0 := by
  have hy : MvPowerSeries.HasSubst (fun (_ : Unit) => y) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusCoordinateQ)
  apply subst_mobiusCoordinateQ_injective
  rw [subst_symmetrizedDescent]
  change A + MvPowerSeries.subst (fun (_ : Unit) => w) A =
    MvPowerSeries.subst (fun (_ : Unit) => y) 0
  rw [subst_pureLogarithmSeries_mobiusInvolutionQ, add_neg_cancel,
    ← MvPowerSeries.substAlgHom_apply hy, map_zero]

theorem symmetrizedDescent_sq_pureLogarithmSeries :
    symmetrizedDescent (A ^ 2) = PowerSeries.C (R := ℚ) (-4) * pureB3Series := by
  have hy : MvPowerSeries.HasSubst (fun (_ : Unit) => y) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusCoordinateQ)
  have hw : MvPowerSeries.HasSubst (fun (_ : Unit) => w) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusInvolutionQ)
  apply subst_mobiusCoordinateQ_injective
  rw [subst_symmetrizedDescent, ← MvPowerSeries.substAlgHom_apply hy, map_mul]
  simp only [map_neg, map_ofNat, MvPowerSeries.substAlgHom_apply]
  change A ^ 2 + MvPowerSeries.subst (fun (_ : Unit) => w) (A ^ 2) = _
  rw [MvPowerSeries.subst_pow hw, subst_pureLogarithmSeries_mobiusInvolutionQ]
  linear_combination 2 * two_mul_subst_pureB3Series

theorem subst_pureB2Series :
    MvPowerSeries.subst (fun (_ : Unit) => y) pureB2Series = 2 * y + δ * A := by
  have hy : MvPowerSeries.HasSubst (fun (_ : Unit) => y) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusCoordinateQ)
  let s : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ := MvPowerSeries.substAlgHom hy
  have hs (g : PowerSeries ℚ) : s g = MvPowerSeries.subst (fun (_ : Unit) => y) g :=
    MvPowerSeries.substAlgHom_apply hy g
  have hsx : s x = y := MvPowerSeries.substAlgHom_X hy ()
  have hd : D (s pureB3Series) = s (D pureB3Series) * D y := by
    rw [hs, hs]
    exact derivativeFun_subst pureB3Series y constantCoeff_mobiusCoordinateQ
  have hfirst : δ * s (D pureB3Series) = A := by
    calc
      _ = ((x - 1) * D y) * s (D pureB3Series) := by
        rw [X_sub_one_mul_derivative_coordinate]
      _ = (x - 1) * D (s pureB3Series) := by rw [hd]; ring
      _ = A := by rw [hs]; exact X_sub_one_mul_derivative_subst_pureB3Series
  rw [← hs]
  simp only [pureB2Series, map_mul, map_sub, map_ofNat, hsx]
  linear_combination -(s (D pureB3Series)) * mobius_difference_sq + δ * hfirst

theorem pureB2Series_eq_symmetrizedDescent :
    pureB2Series = 2 * x + symmetrizedDescent (x * A) := by
  have hy : MvPowerSeries.HasSubst (fun (_ : Unit) => y) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusCoordinateQ)
  have hw : MvPowerSeries.HasSubst (fun (_ : Unit) => w) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusInvolutionQ)
  have h2 : MvPowerSeries.subst (fun (_ : Unit) => y) (2 * x) = 2 * y := by
    rw [← MvPowerSeries.substAlgHom_apply hy]
    simp only [map_mul, map_ofNat]
    congr 1
    exact MvPowerSeries.substAlgHom_X hy ()
  have hxw : MvPowerSeries.subst (fun (_ : Unit) => w) x = w :=
    MvPowerSeries.subst_X hw ()
  apply subst_mobiusCoordinateQ_injective
  rw [subst_pureB2Series, MvPowerSeries.subst_add hy, h2, subst_symmetrizedDescent]
  change 2 * y + δ * A = 2 * y +
    (x * A + MvPowerSeries.subst (fun (_ : Unit) => w) (x * A))
  rw [MvPowerSeries.subst_mul hw, hxw, subst_pureLogarithmSeries_mobiusInvolutionQ]
  ring

/-- The exact minus symmetrization defining B4 in CDT's `defB`. -/
noncomputable def pureB4Series : PowerSeries ℚ :=
  PowerSeries.C (R := ℚ) 2 * symmetrizedDescent (x * L) - x * pureB3Series

theorem subst_pureB4Series :
    MvPowerSeries.subst (fun (_ : Unit) => y) pureB4Series =
      δ * (L - MvPowerSeries.subst (fun (_ : Unit) => w) L) := by
  have hy : MvPowerSeries.HasSubst (fun (_ : Unit) => y) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusCoordinateQ)
  have hw : MvPowerSeries.HasSubst (fun (_ : Unit) => w) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusInvolutionQ)
  have hxy : MvPowerSeries.subst (fun (_ : Unit) => y) x = y :=
    MvPowerSeries.subst_X hy ()
  have hxw : MvPowerSeries.subst (fun (_ : Unit) => w) x = w :=
    MvPowerSeries.subst_X hw ()
  have h2 : MvPowerSeries.subst (fun (_ : Unit) => y) (PowerSeries.C (R := ℚ) 2) = 2 := by
    rw [map_ofNat, ← MvPowerSeries.substAlgHom_apply hy, map_ofNat]
  have hsub (f g : PowerSeries ℚ) :
      MvPowerSeries.subst (fun (_ : Unit) => y) (f - g) =
        MvPowerSeries.subst (fun (_ : Unit) => y) f -
          MvPowerSeries.subst (fun (_ : Unit) => y) g := by
    rw [← MvPowerSeries.substAlgHom_apply hy, map_sub]
    simp only [MvPowerSeries.substAlgHom_apply]
  rw [pureB4Series, hsub, MvPowerSeries.subst_mul hy,
    MvPowerSeries.subst_mul hy, h2, hxy, ← symmetrizedDescent_pureDilogarithmSeries,
    subst_symmetrizedDescent, subst_symmetrizedDescent]
  change 2 * (x * L + MvPowerSeries.subst (fun (_ : Unit) => w) (x * L)) -
    y * (L + MvPowerSeries.subst (fun (_ : Unit) => w) L) = _
  rw [MvPowerSeries.subst_mul hw, hxw]
  dsimp only [mobiusCoordinateQ]
  ring

@[simp]
theorem constantCoeff_pureB4Series : PowerSeries.constantCoeff (R := ℚ) pureB4Series = 0 := by
  simp [pureB4Series, constantCoeff_symmetrizedDescent]

@[simp]
theorem coeff_one_pureB4Series : PowerSeries.coeff (R := ℚ) 1 pureB4Series = -4 := by
  rw [pureB4Series, map_sub, PowerSeries.coeff_C_mul, coeff_one_symmetrizedDescent,
    show 1 = 0 + 1 by rfl, PowerSeries.coeff_succ_X_mul,
    show 2 = 1 + 1 by rfl, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
  norm_num

end DirichletL

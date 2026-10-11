import Analysis.JFunctionOperator
import Analysis.JFunctionFactorial
import Analysis.MobiusDerivatives

/-!
The exact factorial identification of CDT v2, `newfunction`, and its
descent to `defB5` (supplied TeX lines 7358-7387). All substitutions
are formal at zero; the coordinate's derivative is never inverted.
-/

namespace DirichletL

private theorem j_pullback_polynomial {R : Type*} [CommRing R]
    (z u f0 f1 f2 : R) (hu : (1 - z) * u = 1) :
    2 * z * (1 - z) ^ 2 *
        (2 * f1 * (1 - u ^ 2) + z * (f2 * (1 - u ^ 2) ^ 2 + f1 * (-2 * u ^ 3))) +
      (2 - z) * (1 - z) * (f0 + z * (f1 * (1 - u ^ 2))) + z * f0 =
      (1 - z) * (2 * (z + 1 - u) ^ 2 * (4 - (z + 1 - u)) * f2 +
        (z + 1 - u) * (16 - 5 * (z + 1 - u)) * f1 + (2 - (z + 1 - u)) * f0) := by
  linear_combination
    (-f0 + (1 - z) * (11 + (5 - z) * u - 4 * z ^ 2 * u ^ 2) * f1 +
      2 * (1 - z) * (5 * z + 3 - (2 * z ^ 2 + 2) * u - (z + 1) * u ^ 2 +
        z ^ 2 * u ^ 3) * f2) * hu

local notation "D" => PowerSeries.derivative ℚ
local notation "x" => (PowerSeries.X : PowerSeries ℚ)
local notation "y" => mobiusCoordinateQ

/-- The source's LL operator intertwines with the factorial quotient equation. -/
theorem pureJOperator_factorial_pullback (f : PowerSeries ℚ) :
    pureJOperator (x * MvPowerSeries.subst (fun (_ : Unit) => y) f) =
      (1 - x) * MvPowerSeries.subst (fun (_ : Unit) => y) (pureB5QuotientOperator f) := by
  have hy : MvPowerSeries.HasSubst (fun (_ : Unit) => y) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusCoordinateQ)
  let s : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ := MvPowerSeries.substAlgHom hy
  have hsx : s x = y := MvPowerSeries.substAlgHom_X hy ()
  have hs (g : PowerSeries ℚ) : s g = MvPowerSeries.subst (fun (_ : Unit) => y) g :=
    MvPowerSeries.substAlgHom_apply hy g
  have hd (g : PowerSeries ℚ) : D (s g) = s (D g) * D y := by
    rw [hs, hs]
    exact derivativeFun_subst g y constantCoeff_mobiusCoordinateQ
  have hdd (g : PowerSeries ℚ) : D (D (s g)) =
      s (D (D g)) * (D y) ^ 2 + s (D g) * D (D y) := by
    rw [hs, hs, hs]
    exact derivativeFun_subst_two g y constantCoeff_mobiusCoordinateQ
  have h1 : D (x * s f) = s f + x * D (s f) := by
    simp only [Derivation.leibniz, PowerSeries.derivative_X, smul_eq_mul, mul_one]
    ring
  have h2 : D (D (x * s f)) = 2 * D (s f) + x * D (D (s f)) := by
    rw [h1]
    simp only [map_add, Derivation.leibniz, PowerSeries.derivative_X, smul_eq_mul, mul_one]
    ring
  rw [← hs, ← hs]
  have he := j_pullback_polynomial x (1 - mobiusInvolutionQ)
    (s f) (s (D f)) (s (D (D f))) one_sub_X_mul_one_sub_mobiusInvolutionQ
  rw [pureJOperator, h2, h1, hdd, hd,
    derivative_two_mobiusCoordinateQ, derivative_mobiusCoordinateQ]
  simp only [pureB5QuotientOperator, map_add, map_sub, map_mul,
    map_pow, map_ofNat, hsx]
  have hy' : x + 1 - (1 - mobiusInvolutionQ) = y := by
    dsimp only [mobiusCoordinateQ]
    ring
  rw [hy'] at he
  simpa only [mul_assoc] using he

/-- The normalized recurrence J is exactly the factorial pullback in `newfunction`. -/
theorem pureJSeries_eq_factorial_pullback :
    pureJSeries = x * MvPowerSeries.subst (fun (_ : Unit) => y) pureB5QuotientSeries := by
  apply pureJOperator_injective_of_constantCoeff
  · rw [pureJOperator_pureJSeries, pureJOperator_factorial_pullback,
      pureB5QuotientSeries_ode]
    have hy : MvPowerSeries.HasSubst (fun (_ : Unit) => y) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusCoordinateQ)
    rw [← MvPowerSeries.substAlgHom_apply hy, map_ofNat]
    ring
  · simp [pureJSeries]

/-- Positive symmetrization of J is the pullback of the literal B5 series. -/
theorem symmetrizedFormal_pureJSeries :
    symmetrizedFormal pureJSeries =
      MvPowerSeries.subst (fun (_ : Unit) => y) pureB5Series := by
  have hy : MvPowerSeries.HasSubst (fun (_ : Unit) => y) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusCoordinateQ)
  have hw : MvPowerSeries.HasSubst (fun (_ : Unit) => mobiusInvolutionQ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusInvolutionQ)
  have hinv : MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ)
      (MvPowerSeries.subst (fun (_ : Unit) => y) pureB5QuotientSeries) =
      MvPowerSeries.subst (fun (_ : Unit) => y) pureB5QuotientSeries := by
    rw [MvPowerSeries.subst_comp_subst_apply hy hw]
    simp only [subst_mobiusCoordinateQ]
  change pureJSeries + MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ)
    pureJSeries = _
  rw [pureJSeries_eq_factorial_pullback, MvPowerSeries.subst_mul hw, hinv,
    pureB5Series, MvPowerSeries.subst_mul hy]
  have hxw : MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) x =
      mobiusInvolutionQ := MvPowerSeries.subst_X hw ()
  have hxy : MvPowerSeries.subst (fun (_ : Unit) => y) x = y :=
    MvPowerSeries.subst_X hy ()
  rw [hxw, hxy]
  dsimp only [mobiusCoordinateQ]
  ring

theorem symmetrizedDescent_pureJSeries : symmetrizedDescent pureJSeries = pureB5Series := by
  apply subst_mobiusCoordinateQ_injective
  rw [subst_symmetrizedDescent, symmetrizedFormal_pureJSeries]

/-- The trace of XJ is (y-2) times B5. -/
theorem symmetrizedDescent_X_mul_pureJSeries :
    symmetrizedDescent (x * pureJSeries) = (x - 2) * pureB5Series := by
  have hy : MvPowerSeries.HasSubst (fun (_ : Unit) => y) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusCoordinateQ)
  have hw : MvPowerSeries.HasSubst (fun (_ : Unit) => mobiusInvolutionQ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusInvolutionQ)
  have hinv : MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ)
      (MvPowerSeries.subst (fun (_ : Unit) => y) pureB5QuotientSeries) =
      MvPowerSeries.subst (fun (_ : Unit) => y) pureB5QuotientSeries := by
    rw [MvPowerSeries.subst_comp_subst_apply hy hw]
    simp only [subst_mobiusCoordinateQ]
  have hxy : MvPowerSeries.subst (fun (_ : Unit) => y) x = y :=
    MvPowerSeries.subst_X hy ()
  have hxw : MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) x =
      mobiusInvolutionQ := MvPowerSeries.subst_X hw ()
  apply subst_mobiusCoordinateQ_injective
  rw [subst_symmetrizedDescent]
  change x * pureJSeries +
    MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) (x * pureJSeries) = _
  rw [pureJSeries_eq_factorial_pullback, MvPowerSeries.subst_mul hw,
    MvPowerSeries.subst_mul hw, hxw, hinv, pureB5Series,
    MvPowerSeries.subst_mul hy, MvPowerSeries.subst_mul hy, hxy]
  have hsub : MvPowerSeries.subst (fun (_ : Unit) => y) (x - 2) = y - 2 := by
    rw [← MvPowerSeries.substAlgHom_apply hy]
    simp only [map_sub, map_ofNat]
    rw [MvPowerSeries.substAlgHom_apply, hxy]
  rw [hsub]
  dsimp only [mobiusCoordinateQ]
  linear_combination -2 * (MvPowerSeries.subst
    (fun (_ : Unit) => x + mobiusInvolutionQ) pureB5QuotientSeries) *
    X_sub_one_mul_mobiusInvolutionQ

end DirichletL

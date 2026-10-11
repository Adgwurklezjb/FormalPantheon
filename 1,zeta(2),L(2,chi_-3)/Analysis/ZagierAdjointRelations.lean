import Analysis.RationalFunctionCalculus
import Analysis.ZagierDerivativeIndependence
import Analysis.ZagierAdjointGerms

/-!
Coefficient comparison in CDT v2, `14functions`, between `remaining` and
the backward adjoint equations (supplied TeX lines 8140-8166).
-/

namespace DirichletL

open Polynomial Filter Set
open scoped Topology Matrix

/-- The rational coefficients after differentiating and using the homogeneous equation. -/
noncomputable def zagierAdjointRatFuncResidual (B : Fin 4 → RatFunc ℂ) (a b c : ℂ) :
    Fin 4 → RatFunc ℂ :=
  let K (i : Fin 5) := algebraMap ℂ[X] (RatFunc ℂ) (zagierODECoeff i) /
    algebraMap ℂ[X] (RatFunc ℂ) (zagierODECoeff 4)
  let F := algebraMap ℂ[X] (RatFunc ℂ) (C a * X ^ 2 + C b * X + C c) /
    algebraMap ℂ[X] (RatFunc ℂ) (X ^ 2)
  ![ratFuncDerivative (B 0) - K 0 * B 3 - F,
    ratFuncDerivative (B 1) + B 0 - K 1 * B 3,
    ratFuncDerivative (B 2) + B 1 - K 2 * B 3,
    ratFuncDerivative (B 3) + B 2 - K 3 * B 3]

theorem ratFuncEvalGerm_zagierAdjointResidual (B : Fin 4 → RatFunc ℂ) (a b c w : ℂ)
    (i : Fin 4) :
    ratFuncEvalGerm w (zagierAdjointRatFuncResidual B a b c i) =
      (fun z => ![
        deriv (fun x => (B 0).eval (RingHom.id ℂ) x) z -
          (zagierODECoeff 0).eval z / (zagierODECoeff 4).eval z * (B 3).eval (RingHom.id ℂ) z -
            (a + b / z + c / z ^ 2),
        deriv (fun x => (B 1).eval (RingHom.id ℂ) x) z + (B 0).eval (RingHom.id ℂ) z -
          (zagierODECoeff 1).eval z / (zagierODECoeff 4).eval z * (B 3).eval (RingHom.id ℂ) z,
        deriv (fun x => (B 2).eval (RingHom.id ℂ) x) z + (B 1).eval (RingHom.id ℂ) z -
          (zagierODECoeff 2).eval z / (zagierODECoeff 4).eval z * (B 3).eval (RingHom.id ℂ) z,
        deriv (fun x => (B 3).eval (RingHom.id ℂ) x) z + (B 2).eval (RingHom.id ℂ) z -
          (zagierODECoeff 3).eval z / (zagierODECoeff 4).eval z * (B 3).eval (RingHom.id ℂ) z] i :
        ℂ → ℂ) := by
  have h4 : zagierODECoeff 4 ≠ 0 := by
    change (X - 4) ^ 2 * X ^ 3 * (1 + 72 * X) * zagierSingularCubic ≠ 0
    intro h
    have he := congrArg (fun p : ℂ[X] => p.eval 1) h
    norm_num [zagierSingularCubic] at he
  have hK (j : Fin 5) := ratFuncEvalGerm_polynomial_div (zagierODECoeff j) h4 w
  have hF : ratFuncEvalGerm w
      (algebraMap ℂ[X] (RatFunc ℂ) (C a * X ^ 2 + C b * X + C c) /
        algebraMap ℂ[X] (RatFunc ℂ) (X ^ 2)) =
      (fun z => a + b / z + c / z ^ 2 : ℂ → ℂ) := by
    rw [ratFuncEvalGerm_polynomial_div _ (pow_ne_zero 2 X_ne_zero) w]
    apply Germ.coe_eq.mpr
    filter_upwards [eventually_ne_zero_polynomial_eval (p := X) X_ne_zero w] with z hz
    simp only [eval_X] at hz
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
    field_simp [hz]
  fin_cases i <;>
    simp only [zagierAdjointRatFuncResidual, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    simp only [map_sub (ratFuncEvalGerm w), map_add (ratFuncEvalGerm w),
      map_mul (ratFuncEvalGerm w),
      ratFuncEvalGerm_derivative, hK, hF] <;> rfl

theorem deriv_zagierRatFuncPairing (B : Fin 4 → RatFunc ℂ) {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hz : z ∈ zagierODERegularSet)
    (hode : zagierAnalyticODE f z = 0) (hden : ∀ i, (B i).denom.eval z ≠ 0) :
    deriv (fun w => ∑ i, (B i).eval (RingHom.id ℂ) w * zagierODEState f w i) z =
      ∑ i, (deriv (fun w => (B i).eval (RingHom.id ℂ) w) z * zagierODEState f z i +
        (B i).eval (RingHom.id ℂ) z * (zagierODECompanion z *ᵥ zagierODEState f z) i) := by
  exact (HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    ((hasDerivAt_ratFunc_eval (B i) (hden i)).differentiableAt.hasDerivAt).mul
      ((hasDerivAt_pi.mp (hasDerivAt_zagierODEState_of_ode hf hz hode)) i))).deriv

theorem eq_zero_zagierAdjointRatFuncResidual {r : ℝ} (hr : r ∈ Ioo 0 (1 / 9 : ℝ))
    (B : Fin 4 → RatFunc ℂ) {φ : zagierSolutionGerms (mobiusCoordinate r)} (hφ : φ ≠ 0)
    {f : ℂ → ℂ} (hrep : (φ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = f) (a b c : ℂ)
    (hrel : ∀ᶠ z in 𝓝[≠] (mobiusCoordinate r),
      deriv (fun w => ∑ i, (B i).eval (RingHom.id ℂ) w * zagierODEState f w i) z =
        (a + b / z + c / z ^ 2) * f z) : zagierAdjointRatFuncResidual B a b c = 0 := by
  apply eq_zero_of_zagierRatFuncRelation hr _ hφ hrep
  have hm : (f : Germ (𝓝 (mobiusCoordinate r)) ℂ) ∈
      zagierSolutionGerms (mobiusCoordinate r) := by
    rw [← hrep]
    exact φ.property
  obtain ⟨hf, hode⟩ := mem_zagierSolutionGerms_iff.mp hm
  have hE := eventually_all.mpr (fun i : Fin 4 => Germ.coe_eq.mp
    (ratFuncEvalGerm_zagierAdjointResidual B a b c (mobiusCoordinate r) i))
  filter_upwards [hE, hrel, hf.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    hode.filter_mono nhdsWithin_le_nhds,
    (show ∀ᶠ z in 𝓝 (mobiusCoordinate r), z ∈ zagierODERegularSet from
      isOpen_zagierODERegularSet.mem_nhds (mobiusCoordinate_regular_of_mem_Ioo hr)).filter_mono
        nhdsWithin_le_nhds,
    eventually_all.mpr (fun i : Fin 4 =>
      eventually_ne_zero_polynomial_eval (B i).denom_ne_zero (mobiusCoordinate r))]
    with z hEz hz hfz hoz hreg hd
  rw [deriv_zagierRatFuncPairing B hfz hreg hoz hd] at hz
  simp only [hEz, Fin.sum_univ_four, zagierODECompanion_mulVec, zagierODEState,
    Matrix.cons_val, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    div_eq_mul_inv] at hz ⊢
  linear_combination hz

/-- The differentiated normalized relation forces all coefficients to vanish. -/
theorem eq_zero_of_zagierRatFuncPairing_deriv {r : ℝ} (hr : r ∈ Ioo 0 (1 / 9 : ℝ))
    (B : Fin 4 → RatFunc ℂ)
    (hden : ∀ i, ∃ n : ℕ, (B i).denom ∣ (zagierODECoeff 4) ^ n)
    {φ : zagierSolutionGerms (mobiusCoordinate r)} (hφ : φ ≠ 0)
    {f : ℂ → ℂ} (hrep : (φ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = f) (a b c : ℂ)
    (hrel : ∀ᶠ z in 𝓝[≠] (mobiusCoordinate r),
      deriv (fun w => ∑ i, (B i).eval (RingHom.id ℂ) w * zagierODEState f w i) z =
        (a + b / z + c / z ^ 2) * f z) : (∀ i, B i = 0) ∧ a = 0 ∧ b = 0 ∧ c = 0 := by
  have hE := eq_zero_zagierAdjointRatFuncResidual hr B hφ hrep a b c hrel
  have he (i : Fin 4) := ratFuncEvalGerm_zagierAdjointResidual B a b c (mobiusCoordinate r) i
  simp only [hE, Pi.zero_apply, map_zero] at he
  apply eq_zero_of_zagierAdjointSystem_ratFunc_germ_at (mobiusCoordinate r) B hden a b c
  · intro i
    filter_upwards [Germ.coe_eq.mp (he i.succ).symm] with z hz
    fin_cases i <;>
      simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
        Matrix.cons_val_succ, Matrix.cons_val_fin_one] at hz ⊢ <;>
      exact eq_sub_iff_add_eq.mpr (sub_eq_zero.mp hz)
  · filter_upwards [Germ.coe_eq.mp (he 0).symm] with z hz
    change deriv (fun x => (B 0).eval (RingHom.id ℂ) x) z -
      (zagierODECoeff 0).eval z / (zagierODECoeff 4).eval z * (B 3).eval (RingHom.id ℂ) z -
        (a + b / z + c / z ^ 2) = 0 at hz
    exact sub_eq_zero.mp hz

/-- No normalized primitive relation exists with a nonzero coefficient. -/
theorem eq_zero_of_zagierPrimitiveRelation {r : ℝ} (hr : r ∈ Ioo 0 (1 / 9 : ℝ))
    (B : Fin 4 → RatFunc ℂ)
    (hden : ∀ i, ∃ n : ℕ, (B i).denom ∣ (zagierODECoeff 4) ^ n)
    {φ : zagierSolutionGerms (mobiusCoordinate r)} (hφ : φ ≠ 0)
    {f : ℂ → ℂ} (hrep : (φ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = f)
    (J0 J1 J2 : ℂ → ℂ) (a b c : ℂ)
    (h0 : ∀ᶠ z in 𝓝[≠] (mobiusCoordinate r), HasDerivAt J0 (f z) z)
    (h1 : ∀ᶠ z in 𝓝[≠] (mobiusCoordinate r), HasDerivAt J1 (f z / z) z)
    (h2 : ∀ᶠ z in 𝓝[≠] (mobiusCoordinate r), HasDerivAt J2 (f z / z ^ 2) z)
    (hrel : (fun z => a * J0 z + b * J1 z + c * J2 z) =ᶠ[𝓝[≠] (mobiusCoordinate r)]
      fun z => ∑ i, (B i).eval (RingHom.id ℂ) z * zagierODEState f z i) :
    (∀ i, B i = 0) ∧ a = 0 ∧ b = 0 ∧ c = 0 := by
  apply eq_zero_of_zagierRatFuncPairing_deriv hr B hden hφ hrep a b c
  filter_upwards [eventuallyEq_deriv_of_punctured hrel, h0, h1, h2] with z hz h0z h1z h2z
  rw [← hz, (((h0z.const_mul a).fun_add (h1z.const_mul b)).fun_add (h2z.const_mul c)).deriv]
  ring

end DirichletL

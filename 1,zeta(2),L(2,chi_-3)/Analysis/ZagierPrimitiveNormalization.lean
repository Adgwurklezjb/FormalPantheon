import Analysis.RationalFunctionLocalization
import Analysis.ZagierAdjointRelations

/-!
Polynomial-coefficient normalization in CDT v2, `14functions`, equations
`simpleagain`, `todiff`, and `explicitode` (supplied TeX lines 8099-8140).
-/

namespace DirichletL

open Polynomial Filter Set
open scoped Topology Matrix

/-- The canonical coefficient algebra C[y, c_4(y)⁻¹]. -/
noncomputable def zagierRatFuncCoefficients : Subalgebra ℂ[X] (RatFunc ℂ) :=
  ratFuncAway (zagierODECoeff 4) (by
    change (X - 4) ^ 2 * X ^ 3 * (1 + 72 * X) * zagierSingularCubic ≠ 0
    intro h
    have he := congrArg (fun p : ℂ[X] => p.eval 1) h
    norm_num [zagierSingularCubic] at he)

theorem mem_zagierRatFuncCoefficients_iff {B : RatFunc ℂ} :
    B ∈ zagierRatFuncCoefficients ↔ ∃ n : ℕ, B.denom ∣ (zagierODECoeff 4) ^ n :=
  mem_ratFuncAway_iff

/-- The forcing term from the three polynomially weighted primitive derivatives. -/
noncomputable def zagierPrimitiveForcingRatFunc (P : Fin 3 → ℂ[X]) : RatFunc ℂ :=
  algebraMap ℂ[X] (RatFunc ℂ) (P 0 * X ^ 2 + P 1 * X + P 2) /
    algebraMap ℂ[X] (RatFunc ℂ) (X ^ 2)

theorem ratFuncEvalGerm_zagierPrimitiveForcing (P : Fin 3 → ℂ[X]) (w : ℂ) :
    ratFuncEvalGerm w (zagierPrimitiveForcingRatFunc P) =
      (fun z => (P 0).eval z + (P 1).eval z / z + (P 2).eval z / z ^ 2 : ℂ → ℂ) := by
  rw [zagierPrimitiveForcingRatFunc,
    ratFuncEvalGerm_polynomial_div _ (pow_ne_zero 2 X_ne_zero) w]
  apply Germ.coe_eq.mpr
  filter_upwards [eventually_ne_zero_polynomial_eval (p := X) X_ne_zero w] with z hz
  simp only [eval_X] at hz
  simp only [eval_add, eval_mul, eval_pow, eval_X]
  field_simp [hz]

/-- One differentiation of the polynomially weighted primitive relation. -/
noncomputable def zagierPrimitiveRelationStep (P : Fin 3 → ℂ[X])
    (B : Fin 4 → RatFunc ℂ) : Fin 4 → RatFunc ℂ :=
  zagierAdjointRatFuncResidual B 0 0 0 - ![zagierPrimitiveForcingRatFunc P, 0, 0, 0]

theorem zagierPrimitiveRelationStep_mem (P : Fin 3 → ℂ[X]) (B : Fin 4 → RatFunc ℂ)
    (hB : ∀ i, B i ∈ zagierRatFuncCoefficients) (i : Fin 4) :
    zagierPrimitiveRelationStep P B i ∈ zagierRatFuncCoefficients := by
  have hK (j : Fin 5) : algebraMap ℂ[X] (RatFunc ℂ) (zagierODECoeff j) /
      algebraMap ℂ[X] (RatFunc ℂ) (zagierODECoeff 4) ∈ zagierRatFuncCoefficients :=
    polynomial_div_mem_ratFuncAway _ _ ⟨1, by rw [pow_one]⟩
  have hD (j : Fin 4) := ratFuncDerivative_mem_ratFuncAway (hB j)
  have hR (j : Fin 4) : zagierAdjointRatFuncResidual B 0 0 0 j ∈
      zagierRatFuncCoefficients := by
    fin_cases j <;>
      simp only [zagierAdjointRatFuncResidual, Matrix.cons_val_zero', Matrix.cons_val_succ',
        map_zero, zero_mul, zero_add, zero_div, sub_zero]
    · exact zagierRatFuncCoefficients.sub_mem (hD 0)
        (zagierRatFuncCoefficients.mul_mem (hK 0) (hB 3))
    · exact zagierRatFuncCoefficients.sub_mem (zagierRatFuncCoefficients.add_mem (hD 1) (hB 0))
        (zagierRatFuncCoefficients.mul_mem (hK 1) (hB 3))
    · exact zagierRatFuncCoefficients.sub_mem (zagierRatFuncCoefficients.add_mem (hD 2) (hB 1))
        (zagierRatFuncCoefficients.mul_mem (hK 2) (hB 3))
    · exact zagierRatFuncCoefficients.sub_mem (zagierRatFuncCoefficients.add_mem (hD 3) (hB 2))
        (zagierRatFuncCoefficients.mul_mem (hK 3) (hB 3))
  have hF : zagierPrimitiveForcingRatFunc P ∈ zagierRatFuncCoefficients := by
    apply polynomial_div_mem_ratFuncAway
    refine ⟨1, ?_⟩
    rw [pow_one]
    change X ^ 2 ∣ (X - 4) ^ 2 * X ^ 3 * (1 + 72 * X) * zagierSingularCubic
    refine ⟨(X - 4) ^ 2 * X * (1 + 72 * X) * zagierSingularCubic, ?_⟩
    ring
  apply zagierRatFuncCoefficients.sub_mem (hR i)
  fin_cases i
  exacts [hF, zagierRatFuncCoefficients.zero_mem,
    zagierRatFuncCoefficients.zero_mem, zagierRatFuncCoefficients.zero_mem]

theorem zagierPrimitiveRelation_deriv {r : ℝ} (hr : r ∈ Ioo 0 (1 / 9 : ℝ))
    (P : Fin 3 → ℂ[X]) (B : Fin 4 → RatFunc ℂ)
    {φ : zagierSolutionGerms (mobiusCoordinate r)} {f : ℂ → ℂ}
    (hrep : (φ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = f)
    (J : Fin 3 → ℂ → ℂ)
    (hJ : ∀ j, ∀ᶠ z in 𝓝[≠] (mobiusCoordinate r), HasDerivAt (J j) (f z / z ^ (j : ℕ)) z)
    (hrel : (fun z => ∑ j, (P j).eval z * J j z) =ᶠ[𝓝[≠] (mobiusCoordinate r)]
      fun z => ∑ i, (B i).eval (RingHom.id ℂ) z * zagierODEState f z i) :
    (fun z => ∑ j, (P j).derivative.eval z * J j z) =ᶠ[𝓝[≠] (mobiusCoordinate r)]
      fun z => ∑ i, (zagierPrimitiveRelationStep P B i).eval (RingHom.id ℂ) z *
        zagierODEState f z i := by
  have hm : (f : Germ (𝓝 (mobiusCoordinate r)) ℂ) ∈
      zagierSolutionGerms (mobiusCoordinate r) := by
    rw [← hrep]
    exact φ.property
  obtain ⟨hf, hode⟩ := mem_zagierSolutionGerms_iff.mp hm
  have hV (i : Fin 4) :
      ratFuncEvalGerm (mobiusCoordinate r) (![zagierPrimitiveForcingRatFunc P, 0, 0, 0] i) =
        (fun z => ![(P 0).eval z + (P 1).eval z / z + (P 2).eval z / z ^ 2, 0, 0, 0] i :
          ℂ → ℂ) := by
    fin_cases i
    · exact ratFuncEvalGerm_zagierPrimitiveForcing P (mobiusCoordinate r)
    all_goals
      change ratFuncEvalGerm (mobiusCoordinate r) 0 = (fun _ : ℂ => (0 : ℂ))
      rw [map_zero]
      rfl
  have hS (i : Fin 4) := Germ.coe_eq.mp
    ((map_sub (ratFuncEvalGerm (mobiusCoordinate r)) (zagierAdjointRatFuncResidual B 0 0 0 i)
      (![zagierPrimitiveForcingRatFunc P, 0, 0, 0] i)).trans
        (congrArg (fun g => ratFuncEvalGerm (mobiusCoordinate r)
          (zagierAdjointRatFuncResidual B 0 0 0 i) - g) (hV i)))
  have hE := eventually_all.mpr (fun i : Fin 4 => Germ.coe_eq.mp
    (ratFuncEvalGerm_zagierAdjointResidual B 0 0 0 (mobiusCoordinate r) i))
  filter_upwards [eventuallyEq_deriv_of_punctured hrel, eventually_all.mpr hJ,
    eventually_all.mpr hS, hE, hf.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    hode.filter_mono nhdsWithin_le_nhds,
    (show ∀ᶠ z in 𝓝 (mobiusCoordinate r), z ∈ zagierODERegularSet from
      isOpen_zagierODERegularSet.mem_nhds (mobiusCoordinate_regular_of_mem_Ioo hr)).filter_mono
        nhdsWithin_le_nhds,
    eventually_all.mpr (fun i : Fin 4 =>
      eventually_ne_zero_polynomial_eval (B i).denom_ne_zero (mobiusCoordinate r))]
    with z hz hJz hSz hEz hfz hoz hreg hd
  have hL := (HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => ((P j).hasDerivAt z).fun_mul (hJz j))).deriv
  rw [hL, deriv_zagierRatFuncPairing B hfz hreg hoz hd] at hz
  simp only [zagierPrimitiveRelationStep, Pi.sub_apply, hSz, hEz,
    Fin.sum_univ_three, Fin.sum_univ_four, zagierODECompanion_mulVec, zagierODEState,
    Matrix.cons_val, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_div, zero_add, sub_zero,
    Fin.val_zero, Fin.val_one, Fin.coe_ofNat_eq_mod,
    pow_zero, pow_one, div_one, div_eq_mul_inv] at hz ⊢
  norm_num only at hz
  linear_combination hz

/-- Polynomial primitive coefficients and localized derivative coefficients all vanish. -/
theorem eq_zero_of_zagierPolynomialPrimitiveRelation {r : ℝ} (hr : r ∈ Ioo 0 (1 / 9 : ℝ))
    (P : Fin 3 → ℂ[X]) (B : Fin 4 → RatFunc ℂ)
    (hB : ∀ i, B i ∈ zagierRatFuncCoefficients)
    {φ : zagierSolutionGerms (mobiusCoordinate r)} (hφ : φ ≠ 0) {f : ℂ → ℂ}
    (hrep : (φ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = f)
    (J : Fin 3 → ℂ → ℂ)
    (hJ : ∀ j, ∀ᶠ z in 𝓝[≠] (mobiusCoordinate r), HasDerivAt (J j) (f z / z ^ (j : ℕ)) z)
    (hrel : (fun z => ∑ j, (P j).eval z * J j z) =ᶠ[𝓝[≠] (mobiusCoordinate r)]
      fun z => ∑ i, (B i).eval (RingHom.id ℂ) z * zagierODEState f z i) :
    P = 0 ∧ B = 0 := by
  have hconstant (Q : Fin 3 → ℂ[X]) (C : Fin 4 → RatFunc ℂ)
      (hC : ∀ i, C i ∈ zagierRatFuncCoefficients) (hQ : ∀ j, (Q j).derivative = 0)
      (hrel : (fun z => ∑ j, (Q j).eval z * J j z) =ᶠ[𝓝[≠] (mobiusCoordinate r)]
        fun z => ∑ i, (C i).eval (RingHom.id ℂ) z * zagierODEState f z i) :
      Q = 0 ∧ C = 0 := by
    have hpoly (j : Fin 3) := Polynomial.eq_C_of_derivative_eq_zero (hQ j)
    have heval (j : Fin 3) (z : ℂ) : (Q j).eval z = (Q j).coeff 0 := by
      conv_lhs => rw [hpoly j]
      exact eval_C
    obtain ⟨hC', ha, hb, hc⟩ := eq_zero_of_zagierPrimitiveRelation hr C
      (fun i => mem_zagierRatFuncCoefficients_iff.mp (hC i)) hφ hrep
      (J 0) (J 1) (J 2) ((Q 0).coeff 0) ((Q 1).coeff 0) ((Q 2).coeff 0)
      (by simpa using hJ 0) (by simpa using hJ 1) (by simpa using hJ 2) (by
        filter_upwards [hrel] with z hz
        simpa only [Fin.sum_univ_three, heval] using hz)
    refine ⟨?_, funext hC'⟩
    funext j
    fin_cases j
    · change Q 0 = 0
      rw [hpoly 0, ha, map_zero]
    · change Q 1 = 0
      rw [hpoly 1, hb, map_zero]
    · change Q 2 = 0
      rw [hpoly 2, hc, map_zero]
  have h (n : ℕ) : ∀ Q : Fin 3 → ℂ[X], (∀ j, (Q j).natDegree ≤ n) →
      ∀ C : Fin 4 → RatFunc ℂ, (∀ i, C i ∈ zagierRatFuncCoefficients) →
      ((fun z => ∑ j, (Q j).eval z * J j z) =ᶠ[𝓝[≠] (mobiusCoordinate r)]
        fun z => ∑ i, (C i).eval (RingHom.id ℂ) z * zagierODEState f z i) → Q = 0 ∧ C = 0 := by
    induction n with
    | zero =>
      intro Q hn C hC hrel
      exact hconstant Q C hC
        (fun j => derivative_of_natDegree_zero (Nat.eq_zero_of_le_zero (hn j))) hrel
    | succ n ih =>
      intro Q hn C hC hrel
      obtain ⟨hQ, _⟩ := ih (fun j => (Q j).derivative)
        (fun j => (natDegree_derivative_le _).trans (by have := hn j; omega))
        (zagierPrimitiveRelationStep Q C) (zagierPrimitiveRelationStep_mem Q C hC)
        (zagierPrimitiveRelation_deriv hr Q C hrep J hJ hrel)
      exact hconstant Q C hC (fun j => congrFun hQ j) hrel
  exact h (Finset.univ.sup fun j => (P j).natDegree) P
    (fun j => Finset.le_sup (f := fun j => (P j).natDegree) (Finset.mem_univ j)) B hB hrel

end DirichletL

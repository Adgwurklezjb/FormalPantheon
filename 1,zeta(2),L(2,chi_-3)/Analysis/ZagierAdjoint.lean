import Analysis.ZagierSingularities

/-!
Rational representatives of the backward differential system in CDT v2,
proof of Lemma `14functions`, equations `remaining` through `degree12`.
The source pole-order bounds leading to `b3eq` are separate obligations.
-/

namespace DirichletL

open Polynomial Filter
open scoped Topology

/-- Denominators matching the four backward adjoint numerators. -/
noncomputable def zagierAdjointDenominator : Fin 4 → ℂ[X] :=
  ![72 * X * zagierSingularCubic ^ 3, 72 * zagierSingularCubic ^ 2,
    72 * zagierSingularCubic, 72 * zagierSingularCubic]

/-- The rational candidates obtained by solving backward from CDT equation `b3eq`. -/
noncomputable def zagierAdjointFunction (Q : ℂ[X]) (i : Fin 4) (z : ℂ) : ℂ :=
  (zagierAdjointNumerator Q i).eval z / (zagierAdjointDenominator i).eval z

private theorem leading_coeff_eq :
    zagierODECoeff 4 = X * zagierAdjointSeed * zagierSingularCubic := by
  change (X - 4) ^ 2 * X ^ 3 * (1 + 72 * X) * zagierSingularCubic =
    X * (X ^ 2 * (X - 4) ^ 2 * (1 + 72 * X)) * zagierSingularCubic
  ring

private theorem denominator_factors {z : ℂ} (hz : (zagierODECoeff 4).eval z ≠ 0) :
    z ≠ 0 ∧ zagierAdjointSeed.eval z ≠ 0 ∧ zagierSingularCubic.eval z ≠ 0 := by
  rw [leading_coeff_eq, eval_mul, eval_mul, eval_X] at hz
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).1).2, (mul_ne_zero_iff.mp hz).2⟩

private theorem denominator_ne_zero {z : ℂ} (hz : (zagierODECoeff 4).eval z ≠ 0)
    (i : Fin 4) : (zagierAdjointDenominator i).eval z ≠ 0 := by
  obtain ⟨hx, _, hp⟩ := denominator_factors hz
  fin_cases i <;> simp [zagierAdjointDenominator, hx, hp]

theorem differentiableAt_zagierAdjointFunction (Q : ℂ[X]) (i : Fin 4) {z : ℂ}
    (hz : (zagierODECoeff 4).eval z ≠ 0) :
    DifferentiableAt ℂ (zagierAdjointFunction Q i) z :=
  (zagierAdjointNumerator Q i).differentiableAt.div
    (zagierAdjointDenominator i).differentiableAt (denominator_ne_zero hz i)

private theorem deriv_adjoint (Q : ℂ[X]) (i : Fin 4) {z : ℂ}
    (hz : (zagierODECoeff 4).eval z ≠ 0) :
    deriv (zagierAdjointFunction Q i) z =
      ((zagierAdjointNumerator Q i).derivative.eval z * (zagierAdjointDenominator i).eval z -
        (zagierAdjointNumerator Q i).eval z * (zagierAdjointDenominator i).derivative.eval z) /
      (zagierAdjointDenominator i).eval z ^ 2 :=
  ((zagierAdjointNumerator Q i).hasDerivAt z).div
    ((zagierAdjointDenominator i).hasDerivAt z) (denominator_ne_zero hz i) |>.deriv

/-- The index-3 representative is exactly the source candidate, including its normalization. -/
theorem zagierAdjointFunction_three (Q : ℂ[X]) (z : ℂ) :
    zagierAdjointFunction Q 3 z =
      z ^ 2 * (z - 4) ^ 2 * (z + 1 / 72) * Q.eval z / zagierSingularCubic.eval z := by
  simp [zagierAdjointFunction, zagierAdjointNumerator, zagierAdjointDenominator,
    zagierAdjointSeed, div_eq_mul_inv]
  ring

private theorem numerator_two_identity (Q : ℂ[X]) :
    X * zagierSingularCubic * zagierAdjointNumerator Q 2 =
      zagierODECoeff 3 * Q - X * zagierSingularCubic * (zagierAdjointNumerator Q 3).derivative +
        X * zagierSingularCubic.derivative * zagierAdjointNumerator Q 3 := by
  change X * zagierSingularCubic *
    ((48 * X + 5732 * X ^ 2 - 3164 * X ^ 3 + 432 * X ^ 4) * Q -
      zagierAdjointSeed * Q.derivative) =
    2 * (X - 4) * X ^ 2 * (10 + 204 * X - 118195 * X ^ 2 + 146946 * X ^ 3 -
      142848 * X ^ 4 + 41472 * X ^ 5) * Q -
      X * zagierSingularCubic * (zagierAdjointSeed * Q).derivative +
      X * zagierSingularCubic.derivative * (zagierAdjointSeed * Q)
  simp only [zagierAdjointSeed, zagierSingularCubic,
    derivative_add, derivative_sub, derivative_mul, derivative_pow, derivative_X,
    derivative_ofNat, derivative_one, derivative_neg, C_eq_natCast, zero_mul, mul_zero, one_mul, mul_one,
    add_zero, zero_add, sub_zero, pow_zero, pow_one]
  ring

private theorem numerator_one_identity (Q : ℂ[X]) :
    X * zagierAdjointNumerator Q 1 =
      zagierODECoeff 2 * Q - X * zagierSingularCubic * (zagierAdjointNumerator Q 2).derivative +
        X * zagierSingularCubic.derivative * zagierAdjointNumerator Q 2 := by
  let J : ℂ[X] := -34 - 6353 * X + 690355 * X ^ 2 - 1065613 * X ^ 3 + 867876 * X ^ 4 -
    438336 * X ^ 5 + 72576 * X ^ 6
  change X * (2 * J * Q - zagierSingularCubic * (zagierAdjointNumerator Q 2).derivative +
      zagierSingularCubic.derivative * zagierAdjointNumerator Q 2) =
    2 * X * J * Q - X * zagierSingularCubic * (zagierAdjointNumerator Q 2).derivative +
      X * zagierSingularCubic.derivative * zagierAdjointNumerator Q 2
  ring

private theorem numerator_zero_identity (Q : ℂ[X]) :
    zagierAdjointNumerator Q 0 = zagierODECoeff 1 * zagierSingularCubic * Q -
      X * zagierSingularCubic * (zagierAdjointNumerator Q 1).derivative +
        2 * X * zagierSingularCubic.derivative * zagierAdjointNumerator Q 1 := rfl

/-- The three backward adjoint equations hold off the source singular set. -/
theorem deriv_zagierAdjointFunction_succ (Q : ℂ[X]) (i : Fin 3) {z : ℂ}
    (hz : (zagierODECoeff 4).eval z ≠ 0) :
    deriv (zagierAdjointFunction Q i.succ) z =
      (zagierODECoeff i.succ.castSucc).eval z / (zagierODECoeff 4).eval z *
        zagierAdjointFunction Q 3 z - zagierAdjointFunction Q i.castSucc z := by
  obtain ⟨hx, hk, hp⟩ := denominator_factors hz
  have hb₃ : zagierAdjointNumerator Q 3 = zagierAdjointSeed * Q := rfl
  have hd₁ : (zagierAdjointDenominator 1).derivative =
      144 * zagierSingularCubic * zagierSingularCubic.derivative := by
    change (72 * zagierSingularCubic ^ 2).derivative = _
    rw [derivative_mul, derivative_pow, derivative_ofNat]
    simp only [zero_mul, zero_add, C_eq_natCast]
    ring
  have hd₂ : (zagierAdjointDenominator 2).derivative =
      72 * zagierSingularCubic.derivative := by
    change (72 * zagierSingularCubic).derivative = _
    rw [derivative_mul, derivative_ofNat]
    simp
  have hd₃ : (zagierAdjointDenominator 3).derivative =
      72 * zagierSingularCubic.derivative := hd₂
  fin_cases i
  · change deriv (zagierAdjointFunction Q 1) z =
      (zagierODECoeff 1).eval z / (zagierODECoeff 4).eval z *
        zagierAdjointFunction Q 3 z - zagierAdjointFunction Q 0 z
    rw [deriv_adjoint Q 1 hz, hd₁]
    simp only [zagierAdjointFunction, numerator_zero_identity, hb₃, leading_coeff_eq,
      zagierAdjointDenominator, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      eval_mul, eval_add, eval_sub, eval_pow, eval_X, eval_natCast, eval_ofNat]
    field_simp (disch := simp [hx, hk, hp])
    ring
  · change deriv (zagierAdjointFunction Q 2) z =
      (zagierODECoeff 2).eval z / (zagierODECoeff 4).eval z *
        zagierAdjointFunction Q 3 z - zagierAdjointFunction Q 1 z
    have he := congrArg (Polynomial.eval z) (numerator_one_identity Q)
    simp only [eval_mul, eval_sub, eval_add, eval_X] at he
    have hsolve : (zagierAdjointNumerator Q 1).eval z =
        ((zagierODECoeff 2).eval z * Q.eval z -
          z * zagierSingularCubic.eval z * (zagierAdjointNumerator Q 2).derivative.eval z +
          z * zagierSingularCubic.derivative.eval z * (zagierAdjointNumerator Q 2).eval z) / z := by
      apply (eq_div_iff hx).mpr
      linear_combination he
    rw [deriv_adjoint Q 2 hz, hd₂]
    simp only [zagierAdjointFunction, hsolve, hb₃, leading_coeff_eq,
      zagierAdjointDenominator, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      eval_mul, eval_pow, eval_X, eval_natCast, eval_ofNat]
    field_simp (disch := simp [hx, hk, hp])
    ring
  · change deriv (zagierAdjointFunction Q 3) z =
      (zagierODECoeff 3).eval z / (zagierODECoeff 4).eval z *
        zagierAdjointFunction Q 3 z - zagierAdjointFunction Q 2 z
    have he := congrArg (Polynomial.eval z) (numerator_two_identity Q)
    simp only [eval_mul, eval_sub, eval_add, eval_X] at he
    have hsolve : (zagierAdjointNumerator Q 2).eval z =
        ((zagierODECoeff 3).eval z * Q.eval z -
          z * zagierSingularCubic.eval z * (zagierAdjointNumerator Q 3).derivative.eval z +
          z * zagierSingularCubic.derivative.eval z * (zagierAdjointNumerator Q 3).eval z) /
            (z * zagierSingularCubic.eval z) := by
      apply (eq_div_iff (mul_ne_zero hx hp)).mpr
      linear_combination he
    rw [deriv_adjoint Q 3 hz, hd₃]
    simp only [zagierAdjointFunction, hsolve, hb₃, leading_coeff_eq,
      zagierAdjointDenominator, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      eval_mul, eval_pow, eval_X, eval_natCast, eval_ofNat]
    field_simp (disch := simp [hx, hk, hp])
    ring

/-- The remaining adjoint equation has the polynomial residual as its exact numerator. -/
theorem deriv_zagierAdjointFunction_zero (Q : ℂ[X]) {z : ℂ}
    (hz : (zagierODECoeff 4).eval z ≠ 0) :
    deriv (zagierAdjointFunction Q 0) z -
      (zagierODECoeff 0).eval z / (zagierODECoeff 4).eval z * zagierAdjointFunction Q 3 z =
        (zagierAdjointResidual Q).eval z / (72 * z ^ 2 * zagierSingularCubic.eval z ^ 4) := by
  obtain ⟨hx, hk, hp⟩ := denominator_factors hz
  have hb₃ : zagierAdjointNumerator Q 3 = zagierAdjointSeed * Q := rfl
  have hd₀ : (zagierAdjointDenominator 0).derivative =
      72 * zagierSingularCubic ^ 3 +
        216 * X * zagierSingularCubic ^ 2 * zagierSingularCubic.derivative := by
    change (72 * X * zagierSingularCubic ^ 3).derivative = _
    rw [derivative_mul, derivative_mul, derivative_pow, derivative_ofNat, derivative_X]
    simp only [zero_mul, zero_add, mul_one, C_eq_natCast]
    ring
  rw [deriv_adjoint Q 0 hz, hd₀]
  simp only [zagierAdjointFunction, hb₃, leading_coeff_eq, zagierAdjointResidual,
    zagierAdjointDenominator, Matrix.cons_val_zero, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, eval_mul, eval_add, eval_sub, eval_pow, eval_X,
    eval_natCast, eval_ofNat]
  field_simp (disch := simp [hx, hk, hp])
  ring

/-- The leading coefficient is nonzero on a sufficiently small punctured neighborhood. -/
theorem eventually_ne_zero_zagierODECoeff_four :
    ∀ᶠ z : ℂ in 𝓝[≠] 0, (zagierODECoeff 4).eval z ≠ 0 := by
  let T : ℂ[X] := (X - 4) ^ 2 * (1 + 72 * X) * zagierSingularCubic
  have hT₀ : T.eval 0 ≠ 0 := by norm_num [T, zagierSingularCubic]
  have hT := T.continuous.continuousAt.eventually_ne hT₀
  have hc : zagierODECoeff 4 = X ^ 3 * T := by
    change (X - 4) ^ 2 * X ^ 3 * (1 + 72 * X) * zagierSingularCubic = X ^ 3 * T
    dsimp [T]
    ring
  filter_upwards [hT.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hT hz
  change z ≠ 0 at hz
  rw [hc, eval_mul, eval_pow, eval_X]
  exact mul_ne_zero (pow_ne_zero 3 hz) hT

private theorem polynomial_eq_of_punctured (p q : ℂ[X])
    (h : (fun z => p.eval z) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => q.eval z)) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  obtain ⟨s, hs, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h
  exact ((infinite_of_mem_nhds (0 : ℂ) hs).diff (Set.finite_singleton 0)).mono hsub

/-- The candidate residual cannot equal a nonzero combination of `1`, `1/z`, and `1/z^2`. -/
theorem eq_zero_of_zagierAdjointFunction_relation (Q : ℂ[X]) (hQ : Q.natDegree ≤ 2)
    (a b c : ℂ)
    (h : ∀ᶠ z : ℂ in 𝓝[≠] 0, deriv (zagierAdjointFunction Q 0) z -
      (zagierODECoeff 0).eval z / (zagierODECoeff 4).eval z * zagierAdjointFunction Q 3 z =
        a + b / z + c / z ^ 2) : Q = 0 ∧ a = 0 ∧ b = 0 ∧ c = 0 := by
  apply eq_zero_of_zagierAdjointResidual_eq_of_natDegree_le Q hQ a b c
  apply polynomial_eq_of_punctured
  filter_upwards [h, eventually_ne_zero_zagierODECoeff_four] with z he hz
  obtain ⟨hx, _, hp⟩ := denominator_factors hz
  rw [deriv_zagierAdjointFunction_zero Q hz] at he
  have hd : 72 * z ^ 2 * zagierSingularCubic.eval z ^ 4 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (pow_ne_zero 4 hp)
  rw [(div_eq_iff hd).mp he]
  simp only [eval_mul, eval_add, eval_C, eval_X, eval_pow, eval_natCast, eval_ofNat]
  field_simp [hx]

private theorem eventually_deriv_eq_of_punctured {f g : ℂ → ℂ}
    (h : f =ᶠ[𝓝[≠] (0 : ℂ)] g) : deriv f =ᶠ[𝓝[≠] (0 : ℂ)] deriv g := by
  have h' := eventually_eventually_nhdsWithin.mpr h
  filter_upwards [h', self_mem_nhdsWithin] with z hz hz₀
  rw [nhdsWithin_eq_nhds.mpr (isOpen_compl_singleton.mem_nhds hz₀)] at hz
  exact Filter.EventuallyEq.deriv_eq hz

/-- The three backward equations determine all coefficients from the candidate `b_3`. -/
theorem zagierAdjointFunction_unique (Q : ℂ[X]) (F : Fin 4 → ℂ → ℂ)
    (h3 : F 3 =ᶠ[𝓝[≠] (0 : ℂ)] zagierAdjointFunction Q 3)
    (hrec : ∀ i : Fin 3, ∀ᶠ z : ℂ in 𝓝[≠] 0, deriv (F i.succ) z =
      (zagierODECoeff i.succ.castSucc).eval z / (zagierODECoeff 4).eval z * F 3 z - F i.castSucc z)
    (i : Fin 4) : F i =ᶠ[𝓝[≠] (0 : ℂ)] zagierAdjointFunction Q i := by
  have step (j : Fin 3)
      (hj : F j.succ =ᶠ[𝓝[≠] (0 : ℂ)] zagierAdjointFunction Q j.succ) :
      F j.castSucc =ᶠ[𝓝[≠] (0 : ℂ)] zagierAdjointFunction Q j.castSucc := by
    filter_upwards [hrec j, eventually_deriv_eq_of_punctured hj, h3,
      eventually_ne_zero_zagierODECoeff_four] with z he hd h3 hz
    have hb := deriv_zagierAdjointFunction_succ Q j hz
    rw [hd, h3] at he
    linear_combination he - hb
  have h2 := step 2 h3
  have h1 := step 1 h2
  have h0 := step 0 h1
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- CDT's rational adjoint system has only the zero candidate after the source degree bound. -/
theorem eq_zero_of_zagierAdjointSystem (Q : ℂ[X]) (hQ : Q.natDegree ≤ 2)
    (F : Fin 4 → ℂ → ℂ) (a b c : ℂ)
    (h3 : F 3 =ᶠ[𝓝[≠] (0 : ℂ)] zagierAdjointFunction Q 3)
    (hrec : ∀ i : Fin 3, ∀ᶠ z : ℂ in 𝓝[≠] 0, deriv (F i.succ) z =
      (zagierODECoeff i.succ.castSucc).eval z / (zagierODECoeff 4).eval z * F 3 z - F i.castSucc z)
    (hzero : ∀ᶠ z : ℂ in 𝓝[≠] 0, deriv (F 0) z -
      (zagierODECoeff 0).eval z / (zagierODECoeff 4).eval z * F 3 z = a + b / z + c / z ^ 2) :
    Q = 0 ∧ a = 0 ∧ b = 0 ∧ c = 0 := by
  have h0 := zagierAdjointFunction_unique Q F h3 hrec 0
  apply eq_zero_of_zagierAdjointFunction_relation Q hQ a b c
  filter_upwards [hzero, eventually_deriv_eq_of_punctured h0, h3] with z hz hd h3
  rwa [hd, h3] at hz

/-- The numerator bounds preceding CDT equation `b3eq` suffice for the adjoint obstruction. -/
theorem eq_zero_of_zagierAdjointSystem_numerator (N : ℂ[X])
    (h0 : X ^ 2 ∣ N) (h4 : (X - 4) ^ 2 ∣ N) (h72 : 1 + 72 * X ∣ N)
    (hdeg : N.natDegree ≤ 7) (F : Fin 4 → ℂ → ℂ) (a b c : ℂ)
    (h3 : F 3 =ᶠ[𝓝[≠] (0 : ℂ)] fun z => N.eval z / (72 * zagierSingularCubic.eval z))
    (hrec : ∀ i : Fin 3, ∀ᶠ z : ℂ in 𝓝[≠] 0, deriv (F i.succ) z =
      (zagierODECoeff i.succ.castSucc).eval z / (zagierODECoeff 4).eval z * F 3 z - F i.castSucc z)
    (hzero : ∀ᶠ z : ℂ in 𝓝[≠] 0, deriv (F 0) z -
      (zagierODECoeff 0).eval z / (zagierODECoeff 4).eval z * F 3 z = a + b / z + c / z ^ 2) :
    N = 0 ∧ a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨Q, hQ, hN⟩ := exists_zagierAdjointCandidate N h0 h4 h72 hdeg
  have hcand : F 3 =ᶠ[𝓝[≠] (0 : ℂ)] zagierAdjointFunction Q 3 := by
    filter_upwards [h3] with z hz
    simpa [zagierAdjointFunction, zagierAdjointNumerator, zagierAdjointDenominator, hN] using hz
  obtain ⟨hQ0, ha, hb, hc⟩ := eq_zero_of_zagierAdjointSystem Q hQ F a b c hcand hrec hzero
  exact ⟨by simp [hN, hQ0], ha, hb, hc⟩

end DirichletL

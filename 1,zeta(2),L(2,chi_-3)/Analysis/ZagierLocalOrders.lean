import Analysis.LocalAdjoint
import Analysis.ZagierSingularities

/-!
Finite-singularity order bounds in CDT v2, proof of Lemma `14functions`,
the backward system and the first four local expansions before `b3eq`.
-/

namespace DirichletL

open Polynomial Filter
open scoped Topology

private theorem eval_derivative_ne_zero_of_rootMultiplicity_one {p : ℂ[X]} {a : ℂ}
    (h : p.rootMultiplicity a = 1) : p.derivative.eval a ≠ 0 := by
  have hp : p ≠ 0 := by rintro rfl; simp at h
  have ha : p.IsRoot a := (rootMultiplicity_pos hp).mp (by omega)
  intro hd
  have hm := (one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨ha, hd⟩
  omega

theorem eval_zagierODECoeff_three_neg_one_div_seventy_two :
    (zagierODECoeff 3).eval (-1 / 72) = 288230971 / 11609505792 := by
  change (2 * (X - 4) * X ^ 2 * (10 + 204 * X - 118195 * X ^ 2 + 146946 * X ^ 3 -
    142848 * X ^ 4 + 41472 * X ^ 5) : ℂ[X]).eval (-1 / 72) = _
  norm_num

theorem eval_derivative_zagierODECoeff_four_neg_one_div_seventy_two :
    (zagierODECoeff 4).derivative.eval (-1 / 72) = 288230971 / 34828517376 := by
  change (((X - 4) ^ 2 * X ^ 3 * (1 + 72 * X) * zagierSingularCubic).derivative).eval
    (-1 / 72) = _
  norm_num [zagierSingularCubic, derivative_mul, derivative_pow, derivative_add,
    derivative_sub, derivative_neg, derivative_ofNat, derivative_one, derivative_X]

theorem zagierODECoeff_three_add_derivative_four :
    zagierODECoeff 3 + (zagierODECoeff 4).derivative =
      zagierSingularCubic * (128 * X ^ 2 + 13740 * X ^ 3 - 8339 * X ^ 4 + 1224 * X ^ 5) := by
  change 2 * (X - 4) * X ^ 2 * (10 + 204 * X - 118195 * X ^ 2 + 146946 * X ^ 3 -
      142848 * X ^ 4 + 41472 * X ^ 5) +
    ((X - 4) ^ 2 * X ^ 3 * (1 + 72 * X) * zagierSingularCubic).derivative = _
  simp only [zagierSingularCubic, derivative_mul, derivative_pow, derivative_add,
    derivative_sub, derivative_neg, derivative_ofNat, derivative_one, derivative_X,
    C_eq_natCast]
  ring

theorem eval_zagierODECoeff_three_of_cubic_root {a : ℂ}
    (ha : zagierSingularCubic.eval a = 0) :
    (zagierODECoeff 3).eval a = -(zagierODECoeff 4).derivative.eval a := by
  have h := congrArg (Polynomial.eval a) zagierODECoeff_three_add_derivative_four
  simp only [eval_add, eval_mul, ha, zero_mul] at h
  exact eq_neg_of_add_eq_zero_left h

private theorem analyticAt_adjoint_rhs (a b c : ℂ) {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ (fun w => a + b / w + c / w ^ 2) z :=
  (analyticAt_const.add (analyticAt_const.div analyticAt_id hz)).add
    (analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero 2 hz))

private theorem regularization_zero :
    ∃ U : Fin 4 → ℂ → ℂ, (∀ i, AnalyticAt ℂ (U i) 0) ∧
      (fun i => U i 0) = ![0, 1 / 4, 17 / 4, 5] ∧
      ∀ i : Fin 4, (fun z => (zagierODECoeff i.castSucc).eval z /
        (zagierODECoeff 4).eval z) =ᶠ[𝓝[≠] 0]
          fun z => (z - 0) ^ ((i : ℤ) - 4) * U i z := by
  let e : ℂ[X] := (X - 4) ^ 2 * (1 + 72 * X) * zagierSingularCubic
  let q : Fin 4 → ℂ[X] := ![X * zagierODECoeff 0, zagierODECoeff 1,
    2 * (-34 - 6353 * X + 690355 * X ^ 2 - 1065613 * X ^ 3 + 867876 * X ^ 4 -
      438336 * X ^ 5 + 72576 * X ^ 6),
    2 * (X - 4) * (10 + 204 * X - 118195 * X ^ 2 + 146946 * X ^ 3 -
      142848 * X ^ 4 + 41472 * X ^ 5)]
  have hd : zagierODECoeff 4 = (X - C 0) ^ 3 * e := by
    change (X - 4) ^ 2 * X ^ 3 * (1 + 72 * X) * zagierSingularCubic = _
    simp only [map_zero, sub_zero, e]
    ring
  have he : e.eval 0 ≠ 0 := by norm_num [e, zagierSingularCubic]
  have hq : ∀ i : Fin 4, (X - C 0) ^ (4 - i.val) * zagierODECoeff i.castSucc =
      (X - C 0) ^ 3 * q i := by
    intro i
    fin_cases i <;> norm_num [q, zagierODECoeff] <;> ring
  obtain ⟨U, hU, hUa, hA⟩ := exists_analytic_regularization_of_factorization
    (fun i => zagierODECoeff i.castSucc) q (zagierODECoeff 4) e 0 3 hd he hq
  refine ⟨U, hU, ?_, hA⟩
  funext i
  rw [hUa]
  fin_cases i <;> norm_num [q, e, zagierODECoeff, zagierSingularCubic]

private theorem regularization_four :
    ∃ U : Fin 4 → ℂ → ℂ, (∀ i, AnalyticAt ℂ (U i) 4) ∧
      (fun i => U i 4) = ![0, 0, 3 / 4, 3] ∧
      ∀ i : Fin 4, (fun z => (zagierODECoeff i.castSucc).eval z /
        (zagierODECoeff 4).eval z) =ᶠ[𝓝[≠] 4]
          fun z => (z - 4) ^ ((i : ℤ) - 4) * U i z := by
  let e : ℂ[X] := X ^ 3 * (1 + 72 * X) * zagierSingularCubic
  let q : Fin 4 → ℂ[X] := ![(X - 4) ^ 2 * zagierODECoeff 0,
    (X - 4) * zagierODECoeff 1, zagierODECoeff 2,
    2 * X ^ 2 * (10 + 204 * X - 118195 * X ^ 2 + 146946 * X ^ 3 -
      142848 * X ^ 4 + 41472 * X ^ 5)]
  have hd : zagierODECoeff 4 = (X - C 4) ^ 2 * e := by
    change (X - 4) ^ 2 * X ^ 3 * (1 + 72 * X) * zagierSingularCubic = _
    simp only [map_ofNat, e]
    ring
  have he : e.eval 4 ≠ 0 := by norm_num [e, zagierSingularCubic]
  have hq : ∀ i : Fin 4, (X - C 4) ^ (4 - i.val) * zagierODECoeff i.castSucc =
      (X - C 4) ^ 2 * q i := by
    intro i
    fin_cases i <;> norm_num [q, zagierODECoeff, Matrix.cons_val_two, map_ofNat] <;> ring
  obtain ⟨U, hU, hUa, hA⟩ := exists_analytic_regularization_of_factorization
    (fun i => zagierODECoeff i.castSucc) q (zagierODECoeff 4) e 4 2 hd he hq
  refine ⟨U, hU, ?_, hA⟩
  funext i
  rw [hUa]
  fin_cases i <;> norm_num [q, e, zagierODECoeff, Matrix.cons_val_two, zagierSingularCubic]

theorem two_le_order_zagierAdjointSystem_zero
    (F : Fin 4 → ℂ → ℂ) (a b c : ℂ) (hF : MeromorphicAt (F 3) 0)
    (hrec : ∀ i : Fin 3, ∀ᶠ z in 𝓝[≠] 0,
      deriv (F i.succ) z = (zagierODECoeff i.succ.castSucc).eval z /
        (zagierODECoeff 4).eval z * F 3 z - F i.castSucc z)
    (hzero : (fun z => deriv (F 0) z - (zagierODECoeff 0).eval z /
      (zagierODECoeff 4).eval z * F 3 z) =ᶠ[𝓝[≠] 0] fun z => a + b / z + c / z ^ 2) :
    (2 : WithTop ℤ) ≤ meromorphicOrderAt (F 3) 0 := by
  rcases eq_or_ne (meromorphicOrderAt (F 3) 0) ⊤ with htop | hfin
  · simp [htop]
  obtain ⟨N, hN⟩ := WithTop.ne_top_iff_exists.mp hfin
  rw [← hN]
  by_contra! hlt
  have hlt' : N < 2 := WithTop.coe_lt_coe.mp hlt
  obtain ⟨g, hg, hg0, h3⟩ := (meromorphicOrderAt_eq_int_iff hF).mp hN.symm
  obtain ⟨U, hU, hUa, hA⟩ := regularization_zero
  have hR : AnalyticAt ℂ (fun z => a * z ^ 2 + b * z + c) 0 :=
    ((analyticAt_const.mul (analyticAt_id.pow 2)).add
      (analyticAt_const.mul analyticAt_id)).add analyticAt_const
  have hmul : (fun z => (z - 0) ^ 2 * (deriv (F 0) z -
      (zagierODECoeff 0).eval z / (zagierODECoeff 4).eval z * F 3 z)) =ᶠ[𝓝[≠] 0]
        fun z => a * z ^ 2 + b * z + c := by
    filter_upwards [hzero, self_mem_nhdsWithin] with z hz hzne
    change z ≠ 0 at hzne
    rw [sub_zero, hz]
    field_simp
  have he := adjointIndicial_eq_zero_of_analytic_mul N 2 hg hg0 hU hA
    (by simpa only [smul_eq_mul] using h3) hrec hR hmul (by omega)
  rw [hUa] at he
  have hpoly : adjointIndicial ![0, 1 / 4, 17 / 4, 5] N =
      -(1 / 4 : ℂ) * ((N : ℂ) - 3) ^ 2 * (2 * (N : ℂ) - 5) ^ 2 := by
    simp [adjointIndicial]
    ring
  rw [hpoly] at he
  norm_num [mul_eq_zero, sub_eq_zero] at he
  norm_cast at he
  omega

theorem two_le_order_zagierAdjointSystem_four
    (F : Fin 4 → ℂ → ℂ) (a b c : ℂ) (hF : MeromorphicAt (F 3) 4)
    (hrec : ∀ i : Fin 3, ∀ᶠ z in 𝓝[≠] 4,
      deriv (F i.succ) z = (zagierODECoeff i.succ.castSucc).eval z /
        (zagierODECoeff 4).eval z * F 3 z - F i.castSucc z)
    (hzero : (fun z => deriv (F 0) z - (zagierODECoeff 0).eval z /
      (zagierODECoeff 4).eval z * F 3 z) =ᶠ[𝓝[≠] 4] fun z => a + b / z + c / z ^ 2) :
    (2 : WithTop ℤ) ≤ meromorphicOrderAt (F 3) 4 := by
  rcases eq_or_ne (meromorphicOrderAt (F 3) 4) ⊤ with htop | hfin
  · simp [htop]
  obtain ⟨N, hN⟩ := WithTop.ne_top_iff_exists.mp hfin
  rw [← hN]
  by_contra! hlt
  have hlt' : N < 2 := WithTop.coe_lt_coe.mp hlt
  obtain ⟨g, hg, hg0, h3⟩ := (meromorphicOrderAt_eq_int_iff hF).mp hN.symm
  obtain ⟨U, hU, hUa, hA⟩ := regularization_four
  have he := adjointIndicial_eq_zero_of_analytic N hg hg0 hU hA
    (by simpa only [smul_eq_mul] using h3) hrec
    (analyticAt_adjoint_rhs a b c (by norm_num)) hzero (by omega)
  rw [hUa] at he
  have hpoly : adjointIndicial ![0, 0, 3 / 4, 3] N =
      -(1 / 4 : ℂ) * ((N : ℂ) - 3) * ((N : ℂ) - 2) *
        (2 * (N : ℂ) - 5) * (2 * (N : ℂ) - 3) := by
    simp [adjointIndicial]
    ring
  rw [hpoly] at he
  norm_num [mul_eq_zero, sub_eq_zero] at he
  norm_cast at he
  omega

theorem one_le_order_zagierAdjointSystem_neg_one_div_seventy_two
    (F : Fin 4 → ℂ → ℂ) (a b c : ℂ) (hF : MeromorphicAt (F 3) (-1 / 72))
    (hrec : ∀ i : Fin 3, ∀ᶠ z in 𝓝[≠] (-1 / 72),
      deriv (F i.succ) z = (zagierODECoeff i.succ.castSucc).eval z /
        (zagierODECoeff 4).eval z * F 3 z - F i.castSucc z)
    (hzero : (fun z => deriv (F 0) z - (zagierODECoeff 0).eval z /
      (zagierODECoeff 4).eval z * F 3 z) =ᶠ[𝓝[≠] (-1 / 72)]
        fun z => a + b / z + c / z ^ 2) :
    (1 : WithTop ℤ) ≤ meromorphicOrderAt (F 3) (-1 / 72) := by
  have hd : (zagierODECoeff 4).eval (-1 / 72) = 0 :=
    (eval_zagierODECoeff_four_eq_zero_iff _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hd' : (zagierODECoeff 4).derivative.eval (-1 / 72) ≠ 0 := by
    rw [eval_derivative_zagierODECoeff_four_neg_one_div_seventy_two]
    norm_num
  have hρ : (zagierODECoeff 3).eval (-1 / 72) =
      (3 : ℂ) * (zagierODECoeff 4).derivative.eval (-1 / 72) := by
    rw [eval_zagierODECoeff_three_neg_one_div_seventy_two,
      eval_derivative_zagierODECoeff_four_neg_one_div_seventy_two]
    norm_num
  have h := le_order_adjointSystem_of_simple_root
    (fun i => zagierODECoeff i.castSucc) (zagierODECoeff 4) (-1 / 72) 3 hd hd'
    (by simpa using hρ) F (fun z => a + b / z + c / z ^ 2) hF hrec
    (analyticAt_adjoint_rhs a b c (by norm_num)) hzero
  simpa using h

theorem neg_one_le_order_zagierAdjointSystem_of_cubic_root {w : ℂ}
    (hw : zagierSingularCubic.eval w = 0) (F : Fin 4 → ℂ → ℂ) (a b c : ℂ)
    (hF : MeromorphicAt (F 3) w)
    (hrec : ∀ i : Fin 3, ∀ᶠ z in 𝓝[≠] w,
      deriv (F i.succ) z = (zagierODECoeff i.succ.castSucc).eval z /
        (zagierODECoeff 4).eval z * F 3 z - F i.castSucc z)
    (hzero : (fun z => deriv (F 0) z - (zagierODECoeff 0).eval z /
      (zagierODECoeff 4).eval z * F 3 z) =ᶠ[𝓝[≠] w] fun z => a + b / z + c / z ^ 2) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt (F 3) w := by
  have hd : (zagierODECoeff 4).eval w = 0 :=
    (eval_zagierODECoeff_four_eq_zero_iff _).mpr (Or.inr (Or.inr (Or.inr hw)))
  have hd' := eval_derivative_ne_zero_of_rootMultiplicity_one
    (rootMultiplicity_zagierODECoeff_four_of_cubic_root hw)
  have h := le_order_adjointSystem_of_simple_root
    (fun i => zagierODECoeff i.castSucc) (zagierODECoeff 4) w (-1) hd hd'
    (by simpa using eval_zagierODECoeff_three_of_cubic_root hw)
    F (fun z => a + b / z + c / z ^ 2) hF hrec
    (analyticAt_adjoint_rhs a b c
      (ne_rational_singularities_of_eval_zagierSingularCubic_eq_zero hw).1) hzero
  simpa using h

end DirichletL

import Analysis.RationalFunctionCalculus

/-!
Rational independence of logarithm powers in CDT v2, Lemma `seven`
(supplied TeX lines 7915-7940). The exponential coordinate realizes the
period obstruction with the entire-function identity principle.
-/

namespace DirichletL

open Polynomial Filter Set
open scoped Topology

/-- Exponential periods separate the polynomial coefficients of an entire relation. -/
theorem eq_zero_of_polynomial_one_sub_exp_relation {n : ℕ} (P : Fin n → ℂ[X])
    (h : ∀ t : ℂ, ∑ j, (P j).eval (1 - Complex.exp t) * t ^ (j : ℕ) = 0) : P = 0 := by
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hP (a : ℂ) (ha : a ≠ 1) (j : Fin n) : (P j).eval a = 0 := by
    let l := Complex.log (1 - a)
    let Q : ℂ[X] := ∑ i : Fin n, monomial (i : ℕ) ((P i).eval a)
    have hexp : Complex.exp l = 1 - a := Complex.exp_log (sub_ne_zero.mpr ha.symm)
    have hinj : Function.Injective (fun m : ℕ => l + (m : ℂ) * (2 * Real.pi * Complex.I)) := by
      intro k m he
      exact_mod_cast (mul_right_cancel₀ hc (add_left_cancel he))
    have hroot (m : ℕ) : Q.IsRoot (l + (m : ℂ) * (2 * Real.pi * Complex.I)) := by
      have he := h (l + (m : ℂ) * (2 * Real.pi * Complex.I))
      rw [Complex.exp_periodic.nat_mul m, hexp, sub_sub_cancel] at he
      simpa only [IsRoot, Q, eval_finset_sum, eval_monomial] using he
    have hQ : Q = 0 := Q.eq_zero_of_infinite_isRoot
      ((Set.infinite_range_of_injective hinj).mono (Set.range_subset_iff.mpr hroot))
    have hcoeff := congrArg (fun q : ℂ[X] => q.coeff (j : ℕ)) hQ
    simpa only [Q, finset_sum_coeff, coeff_monomial, Fin.val_inj,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, coeff_zero] using hcoeff
  funext j
  apply (P j).eq_zero_of_infinite_isRoot
  apply ((Set.infinite_univ : (Set.univ : Set ℂ).Infinite).diff (Set.finite_singleton 1)).mono
  intro a ha
  exact hP a ha.2 j

/-- A local polynomial relation among logarithm powers has zero coefficients. -/
theorem eq_zero_of_polynomial_clog_one_sub_relation {n : ℕ} (P : Fin n → ℂ[X])
    (hrel : ∀ᶠ z : ℂ in 𝓝[≠] 0, ∑ j, (P j).eval z * Complex.log (1 - z) ^ (j : ℕ) = 0) :
    P = 0 := by
  have hlog : AnalyticAt ℂ (fun z : ℂ => Complex.log (1 - z)) 0 :=
    (analyticAt_const.sub analyticAt_id).clog (by simp)
  have hsum : AnalyticAt ℂ
      (fun z => ∑ j, (P j).eval z * Complex.log (1 - z) ^ (j : ℕ)) 0 :=
    Finset.univ.analyticAt_fun_sum (fun j _ =>
      ((AnalyticOnNhd.eval_polynomial (P j)) 0 (mem_univ 0)).mul (hlog.pow (j : ℕ)))
  have hfull := hsum.frequently_zero_iff_eventually_zero.mp hrel.frequently
  let F : ℂ → ℂ := fun t => ∑ j, (P j).eval (1 - Complex.exp t) * t ^ (j : ℕ)
  have hF : AnalyticOnNhd ℂ F Set.univ := by
    intro t _
    apply Finset.univ.analyticAt_fun_sum
    intro j _
    exact (((AnalyticOnNhd.eval_polynomial (P j)) _ (mem_univ _)).comp
      (analyticAt_const.sub analyticAt_id.cexp)).mul (analyticAt_id.pow _)
  have hmap : Tendsto (fun t : ℂ => 1 - Complex.exp t) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℂ => 1 - Complex.exp t) :=
      continuous_const.sub Complex.continuous_exp
    simpa only [Complex.exp_zero, sub_self] using
      hc.continuousAt.tendsto (x := (0 : ℂ))
  have hstrip : ∀ᶠ t : ℂ in 𝓝 0, t.im ∈ Ioo (-Real.pi) Real.pi :=
    Complex.continuous_im.continuousAt.preimage_mem_nhds
      (Ioo_mem_nhds (by simpa using neg_neg_of_pos Real.pi_pos) (by simpa using Real.pi_pos))
  have hzero : F =ᶠ[𝓝 0] 0 := by
    filter_upwards [hmap.eventually hfull, hstrip] with t ht hs
    simpa only [F, sub_sub_cancel, Complex.log_exp hs.1 hs.2.le, Pi.zero_apply] using ht
  exact eq_zero_of_polynomial_one_sub_exp_relation P
    (fun t => hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ 0) hzero (mem_univ t))

/-- Rational coefficients, including poles at the germ center, satisfy the same zero criterion. -/
theorem eq_zero_of_ratFunc_clog_one_sub_relation {n : ℕ} (A : Fin n → RatFunc ℂ)
    (hrel : ∀ᶠ z : ℂ in 𝓝[≠] 0,
      ∑ j, (A j).eval (RingHom.id ℂ) z * Complex.log (1 - z) ^ (j : ℕ) = 0) : A = 0 := by
  obtain ⟨q, hq, P, hP⟩ := exists_ratFunc_denominator A
  have hG (p : ℂ[X]) : ratFuncEvalGerm 0 (algebraMap ℂ[X] (RatFunc ℂ) p) =
      (fun z => p.eval z : ℂ → ℂ) := by
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall (fun z => by simp only [RatFunc.eval_algebraMap, Algebra.algebraMap_self_apply, Polynomial.eval₂_id])
  have heval (j : Fin n) : ∀ᶠ z : ℂ in 𝓝[≠] 0,
      (P j).eval z = q.eval z * (A j).eval (RingHom.id ℂ) z := by
    apply Germ.coe_eq.mp
    have he := congrArg (ratFuncEvalGerm 0) (hP j)
    simpa only [map_mul (ratFuncEvalGerm 0), hG] using he
  have hPzero : P = 0 := eq_zero_of_polynomial_clog_one_sub_relation P (by
    filter_upwards [hrel, eventually_all.mpr heval] with z hz hEz
    simp only [hEz, mul_assoc, ← Finset.mul_sum, hz, mul_zero])
  funext j
  have he := hP j
  rw [hPzero, Pi.zero_apply, map_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (RatFunc.algebraMap_ne_zero hq)

/-- Any finite initial family of logarithm powers is independent over C(x). -/
theorem linearIndependent_clog_one_sub_powers (n : ℕ) :
    letI := (ratFuncEvalGerm 0).toModule
    LinearIndependent (RatFunc ℂ) (fun j : Fin n =>
      ((fun z : ℂ => Complex.log (1 - z) ^ (j : ℕ)) : Germ (𝓝[≠] (0 : ℂ)) ℂ)) := by
  letI := (ratFuncEvalGerm 0).toModule
  apply Fintype.linearIndependent_iff.mpr
  intro A hA j
  change ∑ i, ratFuncEvalGerm 0 (A i) *
    ((fun z : ℂ => Complex.log (1 - z) ^ (i : ℕ)) : Germ (𝓝[≠] (0 : ℂ)) ℂ) = 0 at hA
  have he : ((fun z => ∑ i, (A i).eval (RingHom.id ℂ) z *
      Complex.log (1 - z) ^ (i : ℕ)) : Germ (𝓝[≠] (0 : ℂ)) ℂ) =
      ∑ i, ratFuncEvalGerm 0 (A i) *
        ((fun z : ℂ => Complex.log (1 - z) ^ (i : ℕ)) : Germ (𝓝[≠] (0 : ℂ)) ℂ) := by
    rw [show (fun z => ∑ i, (A i).eval (RingHom.id ℂ) z *
      Complex.log (1 - z) ^ (i : ℕ)) =
        ∑ i, (fun z => (A i).eval (RingHom.id ℂ) z * Complex.log (1 - z) ^ (i : ℕ)) by
      funext z
      simp only [Finset.sum_apply]]
    rw [Germ.coe_sum]
    rfl
  exact congrFun (eq_zero_of_ratFunc_clog_one_sub_relation A
    (Germ.coe_eq.mp (he.trans hA))) j

theorem linearIndependent_neg_clog_one_sub_powers (n : ℕ) :
    letI := (ratFuncEvalGerm 0).toModule
    LinearIndependent (RatFunc ℂ) (fun j : Fin n =>
      ((fun z : ℂ => (-Complex.log (1 - z)) ^ (j : ℕ)) : Germ (𝓝[≠] (0 : ℂ)) ℂ)) := by
  letI := (ratFuncEvalGerm 0).toModule
  have h := (linearIndependent_clog_one_sub_powers n).units_smul
    (fun j => Units.mk0 ((-1 : RatFunc ℂ) ^ (j : ℕ)) (pow_ne_zero _ (by norm_num)))
  convert h using 1
  funext j
  change ((fun z : ℂ => (-Complex.log (1 - z)) ^ (j : ℕ)) : Germ (𝓝[≠] (0 : ℂ)) ℂ) =
    ratFuncEvalGerm 0 ((-1 : RatFunc ℂ) ^ (j : ℕ)) *
      ((fun z : ℂ => Complex.log (1 - z) ^ (j : ℕ)) : Germ (𝓝[≠] (0 : ℂ)) ℂ)
  rw [map_pow, map_neg, map_one]
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall (fun z => neg_pow (Complex.log (1 - z)) (j : ℕ))

/-- CDT's first three pure functions, with the signs from `sec:pureX2` (TeX lines 7311-7323). -/
theorem linearIndependent_pureLogarithmicFunctions :
    letI := (ratFuncEvalGerm 0).toModule
    LinearIndependent (RatFunc ℂ)
      ![(1 : Germ (𝓝[≠] (0 : ℂ)) ℂ),
        ((fun z : ℂ => -Complex.log (1 - z)) : Germ (𝓝[≠] (0 : ℂ)) ℂ),
        ((fun z : ℂ => Complex.log (1 - z) ^ 2) : Germ (𝓝[≠] (0 : ℂ)) ℂ)] := by
  letI := (ratFuncEvalGerm 0).toModule
  have he : (fun j : Fin 3 =>
      ((fun z : ℂ => (-Complex.log (1 - z)) ^ (j : ℕ)) : Germ (𝓝[≠] (0 : ℂ)) ℂ)) =
      ![(1 : Germ (𝓝[≠] (0 : ℂ)) ℂ),
        ((fun z : ℂ => -Complex.log (1 - z)) : Germ (𝓝[≠] (0 : ℂ)) ℂ),
        ((fun z : ℂ => Complex.log (1 - z) ^ 2) : Germ (𝓝[≠] (0 : ℂ)) ℂ)] := by
    funext j
    fin_cases j <;> apply Germ.coe_eq.mpr <;>
      exact Eventually.of_forall (fun z => by norm_num [sq])
  rw [← he]
  exact linearIndependent_neg_clog_one_sub_powers 3

end DirichletL

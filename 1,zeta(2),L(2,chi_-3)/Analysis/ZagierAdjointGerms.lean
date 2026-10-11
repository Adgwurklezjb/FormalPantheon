import Analysis.ZagierAdjointBounds
import Analysis.RationalFunctionCalculus

/-!
Rational identity extension in CDT v2, Lemma `14functions`, between
equations `todiff`, `remaining`, and the backward adjoint system.
The equations need hold only on a punctured neighborhood of one complex base.
-/

namespace DirichletL

open Polynomial Filter
open scoped Topology

private theorem polynomial_eq_of_germ (p q : ℂ[X]) (w : ℂ)
    (h : (fun z => p.eval z) =ᶠ[𝓝[≠] w] fun z => q.eval z) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  obtain ⟨s, hs, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h
  exact ((infinite_of_mem_nhds w hs).diff (Set.finite_singleton w)).mono hsub

private theorem quotient_eq_of_germ (p q r s : ℂ[X]) (w : ℂ)
    (h : (fun z => p.eval z / q.eval z) =ᶠ[𝓝[≠] w] fun z => r.eval z / s.eval z)
    (z : ℂ) (hq : q.eval z ≠ 0) (hs : s.eval z ≠ 0) :
    p.eval z / q.eval z = r.eval z / s.eval z := by
  have hq0 : q ≠ 0 := fun h => hq (by simp [h])
  have hs0 : s ≠ 0 := fun h => hs (by simp [h])
  have he : p * s = r * q := by
    apply polynomial_eq_of_germ _ _ w
    filter_upwards [h, eventually_ne_zero_polynomial_eval hq0 w,
      eventually_ne_zero_polynomial_eval hs0 w] with x hx hqx hsx
    simpa only [eval_mul] using (div_eq_div_iff hqx hsx).mp hx
  apply (div_eq_div_iff hq hs).mpr
  simpa only [eval_mul] using congrArg (Polynomial.eval z) he

private theorem derivative_sub_eq_of_germ (p q r s u v : ℂ[X]) (w : ℂ)
    (h : ∀ᶠ z in 𝓝[≠] w, deriv (fun x => p.eval x / q.eval x) z -
      r.eval z / s.eval z = u.eval z / v.eval z)
    (z : ℂ) (hq : q.eval z ≠ 0) (hs : s.eval z ≠ 0) (hv : v.eval z ≠ 0) :
    deriv (fun x => p.eval x / q.eval x) z - r.eval z / s.eval z =
      u.eval z / v.eval z := by
  let P := (p.derivative * q - p * q.derivative) * s - r * q ^ 2
  let Q := q ^ 2 * s
  have hn (x : ℂ) (hqx : q.eval x ≠ 0) (hsx : s.eval x ≠ 0) :
      deriv (fun y => p.eval y / q.eval y) x - r.eval x / s.eval x =
        P.eval x / Q.eval x := by
    rw [((p.hasDerivAt x).fun_div (q.hasDerivAt x) hqx).deriv]
    simp only [P, Q, eval_sub, eval_mul, eval_pow]
    field_simp
  rw [hn z hq hs]
  apply quotient_eq_of_germ P Q u v w ?_ z
    (by simpa only [Q, eval_mul, eval_pow] using mul_ne_zero (pow_ne_zero 2 hq) hs) hv
  have hq0 : q ≠ 0 := fun h => hq (by simp [h])
  have hs0 : s ≠ 0 := fun h => hs (by simp [h])
  filter_upwards [h, eventually_ne_zero_polynomial_eval hq0 w,
    eventually_ne_zero_polynomial_eval hs0 w] with x hx hqx hsx
  exact (hn x hqx hsx).symm.trans hx

private theorem ratFunc_eq_zero_of_germ (B : RatFunc ℂ) {w : ℂ}
    (h : ∀ᶠ z in 𝓝[≠] w, B.eval (RingHom.id ℂ) z = 0) : B = 0 := by
  apply ratFuncEvalGerm_injective w
  rw [map_zero]
  exact Germ.coe_eq.mpr h

private theorem denom_eval_ne_zero (B : RatFunc ℂ)
    (hden : ∃ n : ℕ, B.denom ∣ (zagierODECoeff 4) ^ n)
    {z : ℂ} (hz : (zagierODECoeff 4).eval z ≠ 0) : B.denom.eval z ≠ 0 := by
  obtain ⟨n, hn⟩ := hden
  intro hd
  have he := eval_eq_zero_of_dvd_of_eval_eq_zero hn hd
  rw [eval_pow] at he
  exact hz (pow_eq_zero he)

private theorem eval_derivative (B : RatFunc ℂ) {z : ℂ} (hz : B.denom.eval z ≠ 0) :
    HasDerivAt (fun x => B.eval (RingHom.id ℂ) x)
      ((B.num.derivative.eval z * B.denom.eval z - B.num.eval z * B.denom.derivative.eval z) /
        B.denom.eval z ^ 2) z := by
  exact (B.num.hasDerivAt z).div (B.denom.hasDerivAt z) hz

theorem eq_zero_of_zagierAdjointSystem_ratFunc_germ_at (w : ℂ) (B : Fin 4 → RatFunc ℂ)
    (hden : ∀ i, ∃ n : ℕ, (B i).denom ∣ (zagierODECoeff 4) ^ n) (a b c : ℂ)
    (hrec : ∀ i : Fin 3, ∀ᶠ z in 𝓝[≠] w,
      deriv (fun x => (B i.succ).eval (RingHom.id ℂ) x) z =
        (zagierODECoeff i.succ.castSucc).eval z / (zagierODECoeff 4).eval z *
          (B 3).eval (RingHom.id ℂ) z - (B i.castSucc).eval (RingHom.id ℂ) z)
    (hzero : ∀ᶠ z in 𝓝[≠] w, deriv (fun x => (B 0).eval (RingHom.id ℂ) x) z -
      (zagierODECoeff 0).eval z / (zagierODECoeff 4).eval z * (B 3).eval (RingHom.id ℂ) z =
        a + b / z + c / z ^ 2) : (∀ i, B i = 0) ∧ a = 0 ∧ b = 0 ∧ c = 0 := by
  have hd (i : Fin 4) {z : ℂ} (hz : (zagierODECoeff 4).eval z ≠ 0) :=
    denom_eval_ne_zero (B i) (hden i) hz
  have hrec' (z : ℂ) (hz : (zagierODECoeff 4).eval z ≠ 0) (i : Fin 3) :
      deriv (fun x => (B i.succ).eval (RingHom.id ℂ) x) z =
        (zagierODECoeff i.succ.castSucc).eval z / (zagierODECoeff 4).eval z *
          (B 3).eval (RingHom.id ℂ) z - (B i.castSucc).eval (RingHom.id ℂ) z := by
    have he := derivative_sub_eq_of_germ (B i.succ).num (B i.succ).denom
      (zagierODECoeff i.succ.castSucc * (B 3).num)
      (zagierODECoeff 4 * (B 3).denom) (-(B i.castSucc).num) (B i.castSucc).denom w
      (by
        filter_upwards [hrec i] with x hx
        change deriv (fun y => (B i.succ).num.eval y / (B i.succ).denom.eval y) x =
          (zagierODECoeff i.succ.castSucc).eval x / (zagierODECoeff 4).eval x *
            ((B 3).num.eval x / (B 3).denom.eval x) -
              (B i.castSucc).num.eval x / (B i.castSucc).denom.eval x at hx
        simp only [eval_mul, eval_neg, mul_div_mul_comm, neg_div]
        linear_combination hx)
      z (hd i.succ hz) (by simpa only [eval_mul] using mul_ne_zero hz (hd 3 hz))
      (hd i.castSucc hz)
    simp only [eval_mul, eval_neg, mul_div_mul_comm, neg_div] at he
    change deriv (fun x => (B i.succ).num.eval x / (B i.succ).denom.eval x) z =
      (zagierODECoeff i.succ.castSucc).eval z / (zagierODECoeff 4).eval z *
        ((B 3).num.eval z / (B 3).denom.eval z) -
          (B i.castSucc).num.eval z / (B i.castSucc).denom.eval z
    linear_combination he
  have hzero' (z : ℂ) (hz : (zagierODECoeff 4).eval z ≠ 0) :
      deriv (fun x => (B 0).eval (RingHom.id ℂ) x) z -
        (zagierODECoeff 0).eval z / (zagierODECoeff 4).eval z * (B 3).eval (RingHom.id ℂ) z =
          a + b / z + c / z ^ 2 := by
    have hz0 : z ≠ 0 := by
      intro h
      exact hz (by simp [h, zagierODECoeff])
    have hr (x : ℂ) (hx : x ≠ 0) :
        (C a * X ^ 2 + C b * X + C c).eval x / (X ^ 2 : ℂ[X]).eval x =
          a + b / x + c / x ^ 2 := by
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
      field_simp
    have he := derivative_sub_eq_of_germ (B 0).num (B 0).denom
      (zagierODECoeff 0 * (B 3).num) (zagierODECoeff 4 * (B 3).denom)
      (C a * X ^ 2 + C b * X + C c) (X ^ 2) w
      (by
        filter_upwards [hzero, eventually_ne_zero_polynomial_eval (p := X) (by simp) w]
          with x hx hx0
        rw [hr x (by simpa only [eval_X] using hx0)]
        simpa only [eval_mul, mul_div_mul_comm] using hx)
      z (hd 0 hz) (by simpa only [eval_mul] using mul_ne_zero hz (hd 3 hz))
      (by simpa using pow_ne_zero 2 hz0)
    rw [hr z hz0] at he
    simpa only [eval_mul, mul_div_mul_comm] using he
  obtain ⟨hB3, ha, hb, hc⟩ := eq_zero_of_zagierAdjointSystem_ratFunc (B 3) (hden 3)
    (fun i z => (B i).eval (RingHom.id ℂ) z) a b c (fun _ _ => rfl)
    (fun _ hz i => (eval_derivative (B i) (hd i hz)).differentiableAt) hrec' hzero'
  have hstep (i : Fin 3) (hBi : B i.succ = 0) : B i.castSucc = 0 := by
    apply ratFunc_eq_zero_of_germ
    filter_upwards [hrec i] with z hz
    simpa [hBi, hB3] using hz.symm
  have hB2 : B 2 = 0 := hstep 2 hB3
  have hB1 : B 1 = 0 := hstep 1 hB2
  have hB0 : B 0 = 0 := hstep 0 hB1
  refine ⟨?_, ha, hb, hc⟩
  intro i
  fin_cases i
  exacts [hB0, hB1, hB2, hB3]

theorem eq_zero_of_zagierAdjointSystem_ratFunc_germ (B : Fin 4 → RatFunc ℂ)
    (hden : ∀ i, ∃ n : ℕ, (B i).denom ∣ (zagierODECoeff 4) ^ n) (a b c : ℂ)
    (hrec : ∀ i : Fin 3, ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      deriv (fun x => (B i.succ).eval (RingHom.id ℂ) x) z =
        (zagierODECoeff i.succ.castSucc).eval z / (zagierODECoeff 4).eval z *
          (B 3).eval (RingHom.id ℂ) z - (B i.castSucc).eval (RingHom.id ℂ) z)
    (hzero : ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv (fun x => (B 0).eval (RingHom.id ℂ) x) z -
      (zagierODECoeff 0).eval z / (zagierODECoeff 4).eval z * (B 3).eval (RingHom.id ℂ) z =
        a + b / z + c / z ^ 2) : (∀ i, B i = 0) ∧ a = 0 ∧ b = 0 ∧ c = 0 :=
  eq_zero_of_zagierAdjointSystem_ratFunc_germ_at 0 B hden a b c hrec hzero

theorem eq_zero_of_zagierAdjointSystem_ratFunc_germ_representation
    (B : Fin 4 → RatFunc ℂ)
    (hden : ∀ i, ∃ n : ℕ, (B i).denom ∣ (zagierODECoeff 4) ^ n)
    (F : Fin 4 → ℂ → ℂ) (a b c : ℂ)
    (hrep : ∀ i, F i =ᶠ[𝓝[≠] 0] fun z => (B i).eval (RingHom.id ℂ) z)
    (hrec : ∀ i : Fin 3, ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv (F i.succ) z =
      (zagierODECoeff i.succ.castSucc).eval z / (zagierODECoeff 4).eval z * F 3 z - F i.castSucc z)
    (hzero : ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv (F 0) z -
      (zagierODECoeff 0).eval z / (zagierODECoeff 4).eval z * F 3 z = a + b / z + c / z ^ 2) :
    (∀ i, B i = 0) ∧ a = 0 ∧ b = 0 ∧ c = 0 := by
  apply eq_zero_of_zagierAdjointSystem_ratFunc_germ B hden a b c
  · intro i
    filter_upwards [hrec i, eventuallyEq_deriv_of_punctured (hrep i.succ), hrep 3,
      hrep i.castSucc] with z hz hd h3 hi
    rwa [hd, h3, hi] at hz
  · filter_upwards [hzero, eventuallyEq_deriv_of_punctured (hrep 0), hrep 3] with z hz hd h3
    rwa [hd, h3] at hz

end DirichletL

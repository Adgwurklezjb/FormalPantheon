import Analysis.ZagierAdjoint
import Analysis.ZagierInfinity
import Analysis.ZagierLocalOrders

/-!
Deriving the numerator bounds for CDT v2, Lemma `14functions`, equation `b3eq`,
from the adjoint system on the complement of the finite singular set.
-/

namespace DirichletL

open Polynomial Filter
open scoped Topology

private theorem leading_ne_zero : zagierODECoeff 4 ≠ 0 := by
  intro h
  have hm := rootMultiplicity_zagierODECoeff_four_neg_one_div_seventy_two
  rw [h] at hm
  simp at hm

theorem eq_zero_of_zagierAdjointSystem_rationalForm (N : ℂ[X])
    (F : Fin 4 → ℂ → ℂ) (a b c : ℂ)
    (h3 : ∀ z, (zagierODECoeff 4).eval z ≠ 0 →
      F 3 z = N.eval z / (72 * zagierSingularCubic.eval z))
    (hdiff : ∀ z, (zagierODECoeff 4).eval z ≠ 0 → ∀ i, DifferentiableAt ℂ (F i) z)
    (hrec : ∀ z, (zagierODECoeff 4).eval z ≠ 0 → ∀ i : Fin 3,
      deriv (F i.succ) z = (zagierODECoeff i.succ.castSucc).eval z /
        (zagierODECoeff 4).eval z * F 3 z - F i.castSucc z)
    (hzero : ∀ z, (zagierODECoeff 4).eval z ≠ 0 → deriv (F 0) z -
      (zagierODECoeff 0).eval z / (zagierODECoeff 4).eval z * F 3 z = a + b / z + c / z ^ 2) :
    N = 0 ∧ a = 0 ∧ b = 0 ∧ c = 0 := by
  let D : ℂ[X] := 72 * zagierSingularCubic
  have hD : D ≠ 0 := mul_ne_zero (by norm_num) zagierSingularCubic_separable.ne_zero
  have hm (w : ℂ) : MeromorphicAt (fun z => N.eval z / D.eval z) w :=
    ((AnalyticOnNhd.eval_polynomial N) w (Set.mem_univ w)).meromorphicAt.div
      ((AnalyticOnNhd.eval_polynomial D) w (Set.mem_univ w)).meromorphicAt
  have he (w : ℂ) : F 3 =ᶠ[𝓝[≠] w] fun z => N.eval z / D.eval z := by
    filter_upwards [eventually_ne_zero_polynomial_eval leading_ne_zero w] with z hz
    simpa [D] using h3 z hz
  have hrec' (w : ℂ) (i : Fin 3) : ∀ᶠ z in 𝓝[≠] w,
      deriv (F i.succ) z = (zagierODECoeff i.succ.castSucc).eval z /
        (zagierODECoeff 4).eval z * F 3 z - F i.castSucc z := by
    filter_upwards [eventually_ne_zero_polynomial_eval leading_ne_zero w] with z hz
    exact hrec z hz i
  have hzero' (w : ℂ) : (fun z => deriv (F 0) z - (zagierODECoeff 0).eval z /
      (zagierODECoeff 4).eval z * F 3 z) =ᶠ[𝓝[≠] w] fun z => a + b / z + c / z ^ 2 := by
    filter_upwards [eventually_ne_zero_polynomial_eval leading_ne_zero w] with z hz
    exact hzero z hz
  have hb : X ^ 2 ∣ N ∧ (X - 4) ^ 2 ∣ N ∧ (1 + 72 * X) ∣ N ∧ N.natDegree ≤ 7 := by
    by_cases hN : N = 0
    · simp [hN]
    have ho (w : ℂ) : meromorphicOrderAt (F 3) w =
        (((N.rootMultiplicity w : ℤ) - D.rootMultiplicity w : ℤ) : WithTop ℤ) := by
      rw [meromorphicOrderAt_congr (he w)]
      exact order_polynomial_div hN hD w
    have h0 := two_le_order_zagierAdjointSystem_zero F a b c
      ((hm 0).congr (he 0).symm) (hrec' 0) (hzero' 0)
    have h4 := two_le_order_zagierAdjointSystem_four F a b c
      ((hm 4).congr (he 4).symm) (hrec' 4) (hzero' 4)
    have h72 := one_le_order_zagierAdjointSystem_neg_one_div_seventy_two F a b c
      ((hm (-1 / 72)).congr (he (-1 / 72)).symm) (hrec' (-1 / 72)) (hzero' (-1 / 72))
    have hD0 : D.rootMultiplicity 0 = 0 := rootMultiplicity_eq_zero (by
      norm_num [D, zagierSingularCubic])
    have hD4 : D.rootMultiplicity 4 = 0 := rootMultiplicity_eq_zero (by
      norm_num [D, zagierSingularCubic])
    have hD72 : D.rootMultiplicity (-1 / 72) = 0 := rootMultiplicity_eq_zero (by
      norm_num [D, zagierSingularCubic])
    rw [ho 0, hD0] at h0
    rw [ho 4, hD4] at h4
    rw [ho (-1 / 72), hD72] at h72
    simp only [Nat.cast_zero, sub_zero] at h0 h4 h72
    have hm0 : 2 ≤ N.rootMultiplicity 0 := by exact_mod_cast WithTop.coe_le_coe.mp h0
    have hm4 : 2 ≤ N.rootMultiplicity 4 := by exact_mod_cast WithTop.coe_le_coe.mp h4
    have hm72 : 1 ≤ N.rootMultiplicity (-1 / 72) := by
      exact_mod_cast WithTop.coe_le_coe.mp h72
    have hlin : (X - C (-1 / 72)) ∣ N := by
      simpa using (le_rootMultiplicity_iff hN).mp hm72
    have h72poly : (1 + 72 * X : ℂ[X]) = C 72 * (X - C (-1 / 72)) := by
      rw [mul_sub, ← map_mul]
      norm_num [map_ofNat]
      ring
    refine ⟨by simpa using (le_rootMultiplicity_iff hN).mp hm0,
      by simpa using (le_rootMultiplicity_iff hN).mp hm4, ?_, ?_⟩
    · rw [h72poly, C_mul_dvd (by norm_num : (72 : ℂ) ≠ 0)]
      exact hlin
    · have hinv := (meromorphicAt_polynomial_eval_inv N).div
        (meromorphicAt_polynomial_eval_inv D)
      have heinv : (fun z => F 3 z⁻¹) =ᶠ[𝓝[≠] 0]
          fun z => N.eval z⁻¹ / D.eval z⁻¹ := by
        filter_upwards [eventually_ne_zero_polynomial_eval_inv leading_ne_zero] with z hz
        simpa [D] using h3 z⁻¹ hz
      have hb := neg_four_le_order_zagierAdjointSystem_infinity F a b c
        (hinv.congr heinv.symm) (fun i => ?_) (fun i => ?_) ?_
      · rw [meromorphicOrderAt_congr heinv,
          order_polynomial_div_inv hN hD] at hb
        have hdegD : D.natDegree = 3 := by
          dsimp [D, zagierSingularCubic]
          compute_degree!
          norm_num [coeff_one]
        rw [hdegD] at hb
        have hb' := WithTop.coe_le_coe.mp hb
        norm_num at hb'
        omega
      · filter_upwards [eventually_ne_zero_polynomial_eval_inv leading_ne_zero] with z hz
        exact hdiff z⁻¹ hz i
      · filter_upwards [eventually_ne_zero_polynomial_eval_inv leading_ne_zero] with z hz
        exact hrec z⁻¹ hz i
      · filter_upwards [eventually_ne_zero_polynomial_eval_inv leading_ne_zero] with z hz
        exact hzero z⁻¹ hz
  apply eq_zero_of_zagierAdjointSystem_numerator N hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
    F a b c ?_ (hrec' 0) (hzero' 0)
  simpa [D] using he 0

theorem eq_zero_of_zagierAdjointSystem_polynomial_div (p q : ℂ[X]) (hq : q ≠ 0)
    (hpq : IsCoprime p q)
    (hroots : ∀ w, q.eval w = 0 → (zagierODECoeff 4).eval w = 0)
    (F : Fin 4 → ℂ → ℂ) (a b c : ℂ)
    (h3 : ∀ z, (zagierODECoeff 4).eval z ≠ 0 → F 3 z = p.eval z / q.eval z)
    (hdiff : ∀ z, (zagierODECoeff 4).eval z ≠ 0 → ∀ i, DifferentiableAt ℂ (F i) z)
    (hrec : ∀ z, (zagierODECoeff 4).eval z ≠ 0 → ∀ i : Fin 3,
      deriv (F i.succ) z = (zagierODECoeff i.succ.castSucc).eval z /
        (zagierODECoeff 4).eval z * F 3 z - F i.castSucc z)
    (hzero : ∀ z, (zagierODECoeff 4).eval z ≠ 0 → deriv (F 0) z -
      (zagierODECoeff 0).eval z / (zagierODECoeff 4).eval z * F 3 z = a + b / z + c / z ^ 2) :
    p = 0 ∧ a = 0 ∧ b = 0 ∧ c = 0 := by
  by_cases hp : p = 0
  · have hz := eq_zero_of_zagierAdjointSystem_rationalForm 0 F a b c (fun z hz => ?_)
      hdiff hrec hzero
    · exact ⟨hp, hz.2⟩
    · simpa [hp] using h3 z hz
  have hm (w : ℂ) : MeromorphicAt (fun z => p.eval z / q.eval z) w :=
    ((AnalyticOnNhd.eval_polynomial p) w (Set.mem_univ w)).meromorphicAt.div
      ((AnalyticOnNhd.eval_polynomial q) w (Set.mem_univ w)).meromorphicAt
  have he (w : ℂ) : F 3 =ᶠ[𝓝[≠] w] fun z => p.eval z / q.eval z := by
    filter_upwards [eventually_ne_zero_polynomial_eval leading_ne_zero w] with z hz
    exact h3 z hz
  have hrec' (w : ℂ) (i : Fin 3) : ∀ᶠ z in 𝓝[≠] w,
      deriv (F i.succ) z = (zagierODECoeff i.succ.castSucc).eval z /
        (zagierODECoeff 4).eval z * F 3 z - F i.castSucc z := by
    filter_upwards [eventually_ne_zero_polynomial_eval leading_ne_zero w] with z hz
    exact hrec z hz i
  have hzero' (w : ℂ) : (fun z => deriv (F 0) z - (zagierODECoeff 0).eval z /
      (zagierODECoeff 4).eval z * F 3 z) =ᶠ[𝓝[≠] w] fun z => a + b / z + c / z ^ 2 := by
    filter_upwards [eventually_ne_zero_polynomial_eval leading_ne_zero w] with z hz
    exact hzero z hz
  have hdvd : q ∣ zagierSingularCubic := by
    classical
    rw [Splits.dvd_iff_roots_le_roots (IsAlgClosed.splits q) hq
      zagierSingularCubic_separable.ne_zero, Multiset.le_iff_count]
    intro w
    simp only [count_roots]
    by_cases hqw : q.eval w = 0
    · have hpw : p.eval w ≠ 0 := by
        obtain ⟨u, v, h⟩ := hpq
        have hev := congrArg (Polynomial.eval w) h
        simp only [eval_add, eval_mul, eval_one, hqw, mul_zero, add_zero] at hev
        intro hpw
        rw [hpw, mul_zero] at hev
        exact zero_ne_one hev
      have ho : meromorphicOrderAt (F 3) w =
          ((-(q.rootMultiplicity w : ℤ) : ℤ) : WithTop ℤ) := by
        rw [meromorphicOrderAt_congr (he w),
          order_polynomial_div hp hq w, rootMultiplicity_eq_zero hpw]
        simp
      rcases (eval_zagierODECoeff_four_eq_zero_iff w).mp (hroots w hqw) with
        rfl | rfl | rfl | hw
      · have hb := two_le_order_zagierAdjointSystem_zero F a b c
          ((hm 0).congr (he 0).symm) (hrec' 0) (hzero' 0)
        rw [ho] at hb
        have hb' := WithTop.coe_le_coe.mp hb
        omega
      · have hb := two_le_order_zagierAdjointSystem_four F a b c
          ((hm 4).congr (he 4).symm) (hrec' 4) (hzero' 4)
        rw [ho] at hb
        have hb' := WithTop.coe_le_coe.mp hb
        omega
      · have hb := one_le_order_zagierAdjointSystem_neg_one_div_seventy_two F a b c
          ((hm (-1 / 72)).congr (he (-1 / 72)).symm) (hrec' (-1 / 72)) (hzero' (-1 / 72))
        rw [ho] at hb
        have hb' := WithTop.coe_le_coe.mp hb
        omega
      · have hb := neg_one_le_order_zagierAdjointSystem_of_cubic_root hw F a b c
          ((hm w).congr (he w).symm) (hrec' w) (hzero' w)
        rw [ho] at hb
        rw [rootMultiplicity_zagierSingularCubic hw]
        have hb' := WithTop.coe_le_coe.mp hb
        norm_num at hb'
        omega
    · rw [rootMultiplicity_eq_zero hqw]
      exact Nat.zero_le _
  obtain ⟨r, hr⟩ := hdvd
  let N : ℂ[X] := 72 * p * r
  have hN3 : ∀ z, (zagierODECoeff 4).eval z ≠ 0 →
      F 3 z = N.eval z / (72 * zagierSingularCubic.eval z) := by
    intro z hz
    have hPz : zagierSingularCubic.eval z ≠ 0 := by
      intro hP
      exact hz ((eval_zagierODECoeff_four_eq_zero_iff z).mpr (Or.inr (Or.inr (Or.inr hP))))
    have hqr : q.eval z ≠ 0 ∧ r.eval z ≠ 0 := by
      rw [hr, eval_mul] at hPz
      exact mul_ne_zero_iff.mp hPz
    rw [h3 z hz, hr]
    simp only [N, eval_mul, eval_ofNat]
    field_simp [hqr.1, hqr.2]
  obtain ⟨hN, ha, hb, hc⟩ := eq_zero_of_zagierAdjointSystem_rationalForm N F a b c
    hN3 hdiff hrec hzero
  have hr0 : r ≠ 0 := by
    intro hz
    apply zagierSingularCubic_separable.ne_zero
    simp [hr, hz]
  have hp0 : p = 0 := by
    change 72 * p * r = 0 at hN
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hN).resolve_right hr0)).resolve_left (by norm_num)
  exact ⟨hp0, ha, hb, hc⟩

theorem eq_zero_of_zagierAdjointSystem_ratFunc (B : RatFunc ℂ)
    (hden : ∃ n : ℕ, B.denom ∣ (zagierODECoeff 4) ^ n)
    (F : Fin 4 → ℂ → ℂ) (a b c : ℂ)
    (h3 : ∀ z, (zagierODECoeff 4).eval z ≠ 0 → F 3 z = B.eval (RingHom.id ℂ) z)
    (hdiff : ∀ z, (zagierODECoeff 4).eval z ≠ 0 → ∀ i, DifferentiableAt ℂ (F i) z)
    (hrec : ∀ z, (zagierODECoeff 4).eval z ≠ 0 → ∀ i : Fin 3,
      deriv (F i.succ) z = (zagierODECoeff i.succ.castSucc).eval z /
        (zagierODECoeff 4).eval z * F 3 z - F i.castSucc z)
    (hzero : ∀ z, (zagierODECoeff 4).eval z ≠ 0 → deriv (F 0) z -
      (zagierODECoeff 0).eval z / (zagierODECoeff 4).eval z * F 3 z = a + b / z + c / z ^ 2) :
    B = 0 ∧ a = 0 ∧ b = 0 ∧ c = 0 := by
  have hroots : ∀ w, B.denom.eval w = 0 → (zagierODECoeff 4).eval w = 0 := by
    obtain ⟨n, hn⟩ := hden
    intro w hw
    have hpow := eval_eq_zero_of_dvd_of_eval_eq_zero hn hw
    rw [eval_pow] at hpow
    exact pow_eq_zero hpow
  obtain ⟨hB, ha, hb, hc⟩ := eq_zero_of_zagierAdjointSystem_polynomial_div B.num B.denom
    B.denom_ne_zero B.isCoprime_num_denom hroots F a b c
    (fun z hz => by simpa [RatFunc.eval] using h3 z hz) hdiff hrec hzero
  exact ⟨RatFunc.num_eq_zero_iff.mp hB, ha, hb, hc⟩

end DirichletL

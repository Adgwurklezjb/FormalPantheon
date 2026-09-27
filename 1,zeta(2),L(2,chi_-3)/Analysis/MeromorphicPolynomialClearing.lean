import Comparator.Statement

/-!
Polynomial denominator clearing on compact sets, for the common factor in
CDT v2, supplied TeX 4008-4021 (`G pull`). Meanings, the finite-cover argument,
and pointwise pole values are recorded before these proofs in
-/

namespace DirichletL

open scoped Classical

theorem exists_polynomial_clear_at {f : ℂ → ℂ} {x : ℂ}
    (hx : MeromorphicAt f x) (h0 : AnalyticAt ℂ f 0) :
    ∃ P : Polynomial ℂ, P.eval 0 ≠ 0 ∧
      AnalyticAt ℂ (fun z => P.eval z * f z) x := by
  by_cases h : x = 0
  · subst x
    exact ⟨1, by simp, by simpa only [Polynomial.eval_one, one_mul] using h0⟩
  · obtain ⟨n, hn⟩ := hx
    refine ⟨(Polynomial.X - Polynomial.C x) ^ n, ?_, ?_⟩
    · simpa only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, zero_sub] using pow_ne_zero n (neg_ne_zero.mpr h)
    · simpa only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, smul_eq_mul] using hn

theorem exists_polynomial_clear_compact {f : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hf : MeromorphicOn f K) (h0 : AnalyticAt ℂ f 0) :
    ∃ P : Polynomial ℂ, P.eval 0 = 1 ∧
      AnalyticOnNhd ℂ (fun z => P.eval z * f z) K := by
  have hlocal (x : K) := exists_polynomial_clear_at (hf x x.property) h0
  choose P hP0 hP using hlocal
  let U (x : K) : Set ℂ := {z | AnalyticAt ℂ (fun w => (P x).eval w * f w) z}
  have hUo (x : K) : IsOpen (U x) := isOpen_analyticAt ℂ _
  have hcover : K ⊆ ⋃ x, U x := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hP ⟨z, hz⟩⟩
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover U hUo hcover
  let Q : Polynomial ℂ := ∏ x ∈ S, P x
  have hQ0 : Q.eval 0 ≠ 0 := by
    simp only [Q, Polynomial.eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun x _ => hP0 x)
  have hQ : AnalyticOnNhd ℂ (fun z => Q.eval z * f z) K := by
    intro z hz
    obtain ⟨x, hxS, hx⟩ := Set.mem_iUnion₂.mp (hS hz)
    have hr := AnalyticOnNhd.eval_polynomial (𝕜 := ℂ)
      (∏ y ∈ S.erase x, P y) z (Set.mem_univ z)
    have hfac : (∏ y ∈ S.erase x, P y) * P x = Q :=
      Finset.prod_erase_mul S P hxS
    simpa only [← hfac, Polynomial.eval_mul, mul_assoc] using hr.mul hx
  refine ⟨Polynomial.C (Q.eval 0)⁻¹ * Q, ?_, ?_⟩
  · simp only [Polynomial.eval_mul, Polynomial.eval_C, inv_mul_cancel₀ hQ0]
  · intro z hz
    simpa only [Polynomial.eval_mul, Polynomial.eval_C, mul_assoc] using
      (analyticAt_const.mul (hQ z hz) :
        AnalyticAt ℂ (fun w => (Q.eval 0)⁻¹ * (Q.eval w * f w)) z)

theorem exists_common_polynomial_clear_compact {ι : Type*} [Fintype ι]
    (f : ι → ℂ → ℂ) {K : Set ℂ} (hK : IsCompact K)
    (hf : ∀ i, MeromorphicOn (f i) K) (h0 : ∀ i, AnalyticAt ℂ (f i) 0) :
    ∃ P : Polynomial ℂ, P.eval 0 = 1 ∧
      ∀ i, AnalyticOnNhd ℂ (fun z => P.eval z * f i z) K := by
  choose P hP0 hP using fun i => exists_polynomial_clear_compact hK (hf i) (h0 i)
  refine ⟨∏ i, P i, ?_, ?_⟩
  · simp only [Polynomial.eval_prod, hP0, Finset.prod_const_one]
  · intro i z hz
    have hr := AnalyticOnNhd.eval_polynomial (𝕜 := ℂ)
      (∏ j ∈ Finset.univ.erase i, P j) z (Set.mem_univ z)
    have hfac := Finset.prod_erase_mul Finset.univ P (Finset.mem_univ i)
    simpa only [← hfac, Polynomial.eval_mul, mul_assoc] using hr.mul (hP i z hz)

end DirichletL

import Analysis.UnitCirclePrefix

/-!
Empirical averages for the circle discrepancy argument in CDT v2, supplied
TeX 4054-4067, and published UDC Lemma 2.5.9. The normalization, zero cases,
-/

namespace DirichletL

open MeasureTheory
open scoped ComplexConjugate

attribute [local instance] fact_one_pos

/-- The finite empirical mean minus normalized circle Haar integration. -/
noncomputable def circleEmpiricalDeviation {d : ℕ} (t : Fin d → AddCircle (1 : ℝ)) :
    C(AddCircle (1 : ℝ), ℂ) →ₗ[ℂ] ℂ where
  toFun f := (∑ i, f (t i)) / (d : ℂ) - ∫ x, f x ∂AddCircle.haarAddCircle
  map_add' f g := by
    have hi (h : C(AddCircle (1 : ℝ), ℂ)) : Integrable h AddCircle.haarAddCircle := by
      simpa only [integrableOn_univ] using h.continuous.continuousOn.integrableOn_compact
        (μ := AddCircle.haarAddCircle) isCompact_univ
    simp only [ContinuousMap.add_apply, Finset.sum_add_distrib, integral_add (hi f) (hi g)]
    ring
  map_smul' c f := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      ← Finset.mul_sum, integral_const_mul]
    ring

theorem circleEmpiricalDeviation_apply {d : ℕ} (t : Fin d → AddCircle (1 : ℝ))
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    circleEmpiricalDeviation t f = (∑ i, f (t i)) / (d : ℂ) -
      ∫ x, f x ∂AddCircle.haarAddCircle := rfl

theorem norm_circleEmpiricalDeviation_le {d : ℕ} (hd : 0 < d)
    (t : Fin d → AddCircle (1 : ℝ)) (f : C(AddCircle (1 : ℝ), ℂ)) :
    ‖circleEmpiricalDeviation t f‖ ≤ 2 * ‖f‖ := by
  have havg : ‖(∑ i, f (t i)) / (d : ℂ)‖ ≤ ‖f‖ := by
    rw [norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ (Nat.cast_pos.mpr hd)).mpr
    calc
      ‖∑ i, f (t i)‖ ≤ ∑ i, ‖f (t i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin d, ‖f‖ := Finset.sum_le_sum (fun i _ => f.norm_coe_le_norm (t i))
      _ = ‖f‖ * (d : ℝ) := by simp [nsmul_eq_mul, mul_comm]
  have hint : ‖∫ x, f x ∂AddCircle.haarAddCircle‖ ≤ ‖f‖ := by
    simpa only [measureReal_univ_eq_one, mul_one] using
      norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle)
        (Filter.Eventually.of_forall f.norm_coe_le_norm)
  rw [circleEmpiricalDeviation_apply]
  exact (norm_sub_le _ _).trans ((add_le_add havg hint).trans_eq (by ring))

theorem unitCircle_integral_fourier (n : ℤ) :
    (∫ x : AddCircle (1 : ℝ), fourier n x ∂AddCircle.haarAddCircle) =
      if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · simp [hn, fourier_zero]
  · rw [if_neg hn]
    exact integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hn (by norm_num : (0 : ℝ) < 1))

theorem circleEmpiricalDeviation_fourier {d : ℕ} (t : Fin d → AddCircle (1 : ℝ))
    (hd : 0 < d) (n : ℤ) :
    circleEmpiricalDeviation t (fourier n) =
      if n = 0 then 0 else (∑ i, fourier n (t i)) / (d : ℂ) := by
  rw [circleEmpiricalDeviation_apply, unitCircle_integral_fourier]
  by_cases hn : n = 0
  · simp [hn, fourier_zero, Nat.cast_ne_zero.mpr hd.ne']
  · simp only [if_neg hn, sub_zero]

theorem fourier_natCast_eq_pow {T : ℝ} (m : ℕ) (x : AddCircle T) :
    fourier (m : ℤ) x = fourier 1 x ^ m := by
  induction m with
  | zero => simp only [Nat.cast_zero, fourier_zero, pow_zero]
  | succ m ih => rw [Nat.cast_succ, fourier_add, ih, pow_succ]

theorem norm_circleEmpiricalDeviation_fourier_le {d K : ℕ} (hd : 0 < d)
    {a : ℝ} (ha : 0 ≤ a) (t : Fin d → AddCircle (1 : ℝ))
    (hmode : ∀ m : ℕ, 0 < m → m ≤ K → ‖∑ i, fourier 1 (t i) ^ m‖ ≤ a * (d : ℝ))
    (n : ℤ) (hn : n.natAbs ≤ K) : ‖circleEmpiricalDeviation t (fourier n)‖ ≤ a := by
  cases n with
  | ofNat k =>
    rw [circleEmpiricalDeviation_fourier t hd]
    split_ifs with hk
    · simpa only [norm_zero] using ha
    · rw [norm_div, Complex.norm_natCast]
      change ‖∑ i, fourier (k : ℤ) (t i)‖ / (d : ℝ) ≤ a
      simp_rw [fourier_natCast_eq_pow]
      exact (div_le_iff₀ (Nat.cast_pos.mpr hd)).mpr
        (hmode k (Nat.pos_of_ne_zero (fun h => hk (by subst k; rfl))) (by simpa using hn))
  | negSucc k =>
    rw [circleEmpiricalDeviation_fourier t hd, if_neg (by omega : Int.negSucc k ≠ 0),
      norm_div, Complex.norm_natCast]
    rw [show Int.negSucc k = -((k + 1 : ℕ) : ℤ) by omega]
    simp_rw [fourier_neg]
    rw [← map_sum, Complex.norm_conj]
    simp_rw [fourier_natCast_eq_pow]
    exact (div_le_iff₀ (Nat.cast_pos.mpr hd)).mpr
      (hmode (k + 1) (by omega) (by simpa using hn))

end DirichletL

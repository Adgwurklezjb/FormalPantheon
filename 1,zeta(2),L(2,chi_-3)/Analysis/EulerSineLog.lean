import Mathlib

/-!
The logarithmic Euler sine product on the upper half plane. This supplies
the cotangent expansion needed for the weight-three numerators in CDT v2,
Section 11.1, and Zagier (2009), Section 6. The source and branch checks
-/

namespace DirichletL

open Filter
open scoped Topology

/-- The sum of principal logarithms of Euler's sine-product factors. -/
noncomputable def eulerSineLogSum (z : ℂ) : ℂ :=
  ∑' n : ℕ, Complex.log (1 - z ^ 2 / ((n : ℂ) + 1) ^ 2)

theorem eulerSineFactor_mem_slitPlane {z : ℂ} (hz : 0 < z.im) (n : ℕ) :
    1 - z ^ 2 / ((n : ℂ) + 1) ^ 2 ∈ Complex.slitPlane := by
  have ha : ((n : ℂ) + 1) ^ 2 = ((((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  have ha0 : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
  rw [Complex.mem_slitPlane_iff, ha]
  simp only [Complex.sub_re, Complex.one_re, Complex.div_ofReal_re,
    Complex.sub_im, Complex.one_im, Complex.div_ofReal_im, pow_two,
    Complex.mul_re, Complex.mul_im]
  by_cases hr : z.re = 0
  · left
    simp only [hr, zero_mul, zero_sub]
    have := div_nonneg (mul_self_nonneg z.im) ha0.le
    simp only [pow_two] at this
    rw [neg_div]
    linarith
  · right
    rw [zero_sub]
    apply neg_ne_zero.mpr
    apply div_ne_zero
    · rw [mul_comm z.im z.re, ← two_mul]
      exact mul_ne_zero two_ne_zero (mul_ne_zero hr hz.ne')
    · simpa only [pow_two] using ha0.ne'

private theorem summable_eulerSineLog (z : ℂ) :
    Summable (fun n : ℕ => Complex.log (1 - z ^ 2 / ((n : ℂ) + 1) ^ 2)) := by
  simpa only [Nat.cast_one, neg_div, ← sub_eq_add_neg] using
    Complex.summable_log_one_add_of_summable
      (summable_pow_div_add (-z ^ 2) 2 1 (by decide)).of_norm

theorem tendstoLocallyUniformlyOn_eulerSineLogSum :
    TendstoLocallyUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, Complex.log (1 - z ^ 2 / ((n : ℂ) + 1) ^ 2))
      eulerSineLogSum atTop {z : ℂ | 0 < z.im} := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_lt continuous_const Complex.continuous_im)]
  intro K _ hK
  obtain ⟨M, hM, hbound⟩ := hK.isBounded.exists_pos_norm_le
  have hu := summable_pow_div_add ((M : ℂ) ^ 2) 2 1 (by decide)
  simp only [Nat.cast_one] at hu
  have hmajor : ∀ n : ℕ, ∀ z ∈ K,
      ‖-z ^ 2 / ((n : ℂ) + 1) ^ 2‖ ≤ ‖(M : ℂ) ^ 2 / ((n : ℂ) + 1) ^ 2‖ := by
    intro n z hz
    simp only [norm_div, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hM]
    gcongr
    exact hbound z hz
  have hlimit := hu.tendstoUniformlyOn_tsum_nat_log_one_add (K := K)
    (f := fun n z => -z ^ 2 / ((n : ℂ) + 1) ^ 2)
    (Eventually.of_forall hmajor)
  simp only [neg_div, ← sub_eq_add_neg] at hlimit
  exact hlimit

theorem differentiableOn_eulerSineLogSum :
    DifferentiableOn ℂ eulerSineLogSum {z : ℂ | 0 < z.im} := by
  apply tendstoLocallyUniformlyOn_eulerSineLogSum.differentiableOn _
    (isOpen_lt continuous_const Complex.continuous_im)
  apply Eventually.of_forall
  intro N
  apply DifferentiableOn.fun_sum
  intro n _
  apply ((differentiableOn_const 1).sub
    ((differentiableOn_id.pow 2).div_const (((n : ℂ) + 1) ^ 2))).clog
  exact fun z hz => eulerSineFactor_mem_slitPlane hz n

theorem exp_eulerSineLogSum_eq_sin_div {z : ℂ} (hz : 0 < z.im) :
    Complex.exp (eulerSineLogSum z) = Complex.sin (Real.pi * z) / (Real.pi * z) := by
  have hprod := Complex.hasProd_of_hasSum_log
    (fun n => Complex.slitPlane_ne_zero (eulerSineFactor_mem_slitPlane hz n))
    (summable_eulerSineLog z).hasSum
  have hlim := hprod.tendsto_prod_nat
  have heq : (Real.pi : ℂ) * z * Complex.exp (eulerSineLogSum z) =
      Complex.sin (Real.pi * z) :=
    tendsto_nhds_unique (hlim.const_mul ((Real.pi : ℂ) * z))
      (Complex.tendsto_euler_sin_prod z)
  have hz0 : z ≠ 0 := (UpperHalfPlane.mk z hz).ne_zero
  have hp0 : (Real.pi : ℂ) * z ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hz0
  exact (eq_div_iff hp0).mpr (by simpa only [mul_comm] using heq)

end DirichletL

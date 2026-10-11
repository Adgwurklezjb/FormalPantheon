import Analysis.EulerSineLog

/-!
Locally uniform paired partial fractions for cotangent on the upper half
plane, obtained by differentiating Euler's logarithmic sine product.
This supports the weight-three q-expansions in CDT v2, Section 11.1;
-/

namespace DirichletL

open Filter
open scoped Topology

private theorem hasDerivAt_log_eulerSineFactor {z : ℂ} (hz : 0 < z.im) (n : ℕ) :
    HasDerivAt (fun w : ℂ => Complex.log (1 - w ^ 2 / ((n : ℂ) + 1) ^ 2))
      (1 / (z - ((n : ℂ) + 1)) + 1 / (z + ((n : ℂ) + 1))) z := by
  have hm : z - ((n : ℂ) + 1) ≠ 0 := by
    intro h
    exact hz.ne' (by simpa using congrArg Complex.im h)
  have hp : z + ((n : ℂ) + 1) ≠ 0 := by
    intro h
    exact hz.ne' (by simpa using congrArg Complex.im h)
  have ha : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hquad : ((n : ℂ) + 1) ^ 2 - z ^ 2 ≠ 0 := by
    have hmul := mul_ne_zero hm hp
    intro hzero
    apply hmul
    linear_combination -hzero
  have hf := eulerSineFactor_mem_slitPlane hz n
  have h := ((hasDerivAt_const z (1 : ℂ)).sub
    (((hasDerivAt_id z).pow 2).div_const (((n : ℂ) + 1) ^ 2))).clog hf
  simp only [Pi.sub_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one, zero_sub] at h
  convert h using 1
  rw [show 1 - z ^ 2 / ((n : ℂ) + 1) ^ 2 =
    (((n : ℂ) + 1) ^ 2 - z ^ 2) / ((n : ℂ) + 1) ^ 2 by field_simp]
  field_simp [ha, hm, hp, hquad] <;> ring

theorem deriv_eulerSineLogSum {z : ℂ} (hz : 0 < z.im) :
    deriv eulerSineLogSum z = Real.pi * Complex.cot (Real.pi * z) - 1 / z := by
  have hU := (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz
  have hd := differentiableOn_eulerSineLogSum.differentiableAt hU
  have heq : (fun w => Complex.exp (eulerSineLogSum w)) =ᶠ[𝓝 z]
      (fun w => Complex.sin (Real.pi * w) / (Real.pi * w)) := by
    filter_upwards [hU] with w hw using exp_eulerSineLogSum_eq_sin_div hw
  have he : Complex.exp (eulerSineLogSum z) ≠ 0 := Complex.exp_ne_zero _
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz0 : z ≠ 0 := (UpperHalfPlane.mk z hz).ne_zero
  have hs : Complex.sin (Real.pi * z) ≠ 0 := by
    have hquot := (exp_eulerSineLogSum_eq_sin_div hz) ▸ he
    exact (div_ne_zero_iff.mp hquot).1
  calc
    deriv eulerSineLogSum z = logDeriv (fun w => Complex.exp (eulerSineLogSum w)) z := by
      rw [logDeriv_apply, hd.hasDerivAt.cexp.deriv]
      field_simp
    _ = logDeriv (fun w => Complex.sin (Real.pi * w) / (Real.pi * w)) z := by
      rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq,
        exp_eulerSineLogSum_eq_sin_div hz]
    _ = Real.pi * Complex.cot (Real.pi * z) - 1 / z := by
      rw [logDeriv_div z hs (mul_ne_zero hp hz0) (by fun_prop) (by fun_prop)]
      change logDeriv (Complex.sin ∘ fun w : ℂ => Real.pi * w) z -
        logDeriv (fun w : ℂ => Real.pi * w) z = _
      rw [logDeriv_comp Complex.differentiableAt_sin (by fun_prop),
        Complex.logDeriv_sin, deriv_const_mul_field, deriv_id'',
        logDeriv_const_mul z _ hp, logDeriv_id']
      ring

theorem tendstoLocallyUniformlyOn_cotangentPartialSums :
    TendstoLocallyUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N,
        (1 / (z - ((n : ℂ) + 1)) + 1 / (z + ((n : ℂ) + 1))))
      (fun z => Real.pi * Complex.cot (Real.pi * z) - 1 / z)
      atTop {z : ℂ | 0 < z.im} := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hdiff : ∀ N : ℕ, DifferentiableOn ℂ
      (fun z => ∑ n ∈ Finset.range N, Complex.log (1 - z ^ 2 / ((n : ℂ) + 1) ^ 2))
      {z : ℂ | 0 < z.im} := by
    intro N z hz
    apply DifferentiableWithinAt.fun_sum
    exact fun n _ => (hasDerivAt_log_eulerSineFactor hz n).differentiableAt.differentiableWithinAt
  have hlim := tendstoLocallyUniformlyOn_eulerSineLogSum.deriv
    (Eventually.of_forall hdiff) hopen
  apply (hlim.congr _).congr_right
  · exact fun z hz => deriv_eulerSineLogSum hz
  · intro N z hz
    exact (HasDerivAt.fun_sum (fun n (_ : n ∈ Finset.range N) =>
      hasDerivAt_log_eulerSineFactor hz n)).deriv

end DirichletL

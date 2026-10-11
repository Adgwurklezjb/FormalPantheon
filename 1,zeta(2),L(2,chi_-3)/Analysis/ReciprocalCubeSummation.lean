import Analysis.CotangentPartialFractions

/-!
The reciprocal-cube sum obtained by twice differentiating cotangent's
locally uniform partial fractions. This is the analytic input to the
weight-three numerators in CDT v2, Section 11.1. See the declaration and
-/

namespace DirichletL

open Filter
open scoped Topology

/-- The finite reciprocal-power sum over the integer translates from `-N` to `N`. -/
noncomputable def cotangentSymmetricSum (k N : ℕ) (z : ℂ) : ℂ :=
  1 / z ^ (k + 1) + ∑ n ∈ Finset.range N,
    (1 / (z - ((n : ℂ) + 1)) ^ (k + 1) + 1 / (z + ((n : ℂ) + 1)) ^ (k + 1))

private theorem hasDerivAt_one_div_add_real_pow {z : ℂ} (hz : 0 < z.im)
    (a : ℝ) (k : ℕ) :
    HasDerivAt (fun w : ℂ => 1 / (w + a) ^ (k + 1))
      (-((k : ℂ) + 1) / (z + a) ^ (k + 2)) z := by
  have hza : z + a ≠ 0 := by
    intro h
    exact hz.ne' (by simpa using congrArg Complex.im h)
  have hd := (((hasDerivAt_id z).add_const (a : ℂ)).fun_pow (k + 1)).fun_inv
    (pow_ne_zero _ hza)
  convert hd using 1
  · simp only [one_div, id_eq]
  · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, id_eq, mul_one]
    field_simp [hza, pow_add, pow_succ] <;> ring

theorem hasDerivAt_cotangentSymmetricSum {z : ℂ} (hz : 0 < z.im) (k N : ℕ) :
    HasDerivAt (cotangentSymmetricSum k N)
      (-((k : ℂ) + 1) * cotangentSymmetricSum (k + 1) N z) z := by
  have hzero := hasDerivAt_one_div_add_real_pow hz 0 k
  have hp (n : ℕ) := hasDerivAt_one_div_add_real_pow hz ((n : ℝ) + 1) k
  have hm (n : ℕ) := hasDerivAt_one_div_add_real_pow hz (-((n : ℝ) + 1)) k
  simp only [Complex.ofReal_zero, add_zero] at hzero
  simp only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    Complex.ofReal_neg, ← sub_eq_add_neg] at hp hm
  simpa only [cotangentSymmetricSum, mul_add, Finset.mul_sum, mul_one_div, Nat.add_assoc] using
    hzero.fun_add (HasDerivAt.fun_sum
      (fun n (_ : n ∈ Finset.range N) => (hm n).fun_add (hp n)))

private theorem tendstoLocallyUniformlyOn_cotangentSymmetricSum :
    TendstoLocallyUniformlyOn (cotangentSymmetricSum 0)
      (fun z : ℂ => Real.pi * Complex.cot (Real.pi * z)) atTop {z : ℂ | 0 < z.im} := by
  have h := tendstoLocallyUniformlyOn_cotangentPartialSums
  rw [Metric.tendstoLocallyUniformlyOn_iff] at h ⊢
  intro ε hε z hz
  obtain ⟨t, ht, hlim⟩ := h ε hε z hz
  refine ⟨t, ht, ?_⟩
  filter_upwards [hlim] with N hN w hw
  simpa only [cotangentSymmetricSum, zero_add, pow_one, dist_eq_norm, sub_add_eq_sub_sub]
    using hN w hw

theorem tendsto_cotangentSymmetricSum_cube {z : ℂ} (hz : 0 < z.im) :
    Tendsto (fun N => 2 * cotangentSymmetricSum 2 N z) atTop
      (𝓝 (deriv (deriv (fun w : ℂ => Real.pi * Complex.cot (Real.pi * w))) z)) := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hdiff (k N : ℕ) : DifferentiableOn ℂ (cotangentSymmetricSum k N)
      {z : ℂ | 0 < z.im} := fun z hz =>
    (hasDerivAt_cotangentSymmetricSum hz k N).differentiableAt.differentiableWithinAt
  have hlim := (tendstoLocallyUniformlyOn_cotangentSymmetricSum.deriv
    (Eventually.of_forall (hdiff 0)) hopen).deriv
    (Eventually.of_forall (fun N => (hdiff 0 N).deriv hopen)) hopen
  apply (hlim.congr (G := fun N w => 2 * cotangentSymmetricSum 2 N w) _).tendsto_at hz
  intro N w hw
  have heq : deriv (cotangentSymmetricSum 0 N) =ᶠ[𝓝 w]
      (fun v => -cotangentSymmetricSum 1 N v) := by
    filter_upwards [hopen.mem_nhds hw] with v hv
    simpa using (hasDerivAt_cotangentSymmetricSum hv 0 N).deriv
  change deriv (deriv (cotangentSymmetricSum 0 N)) w = _
  rw [heq.deriv_eq, (hasDerivAt_cotangentSymmetricSum hw 1 N).fun_neg.deriv]
  norm_num

theorem summable_norm_one_div_int_add_cube {z : ℂ} (hz : 0 < z.im) :
    Summable (fun n : ℤ => ‖1 / (z + n) ^ 3‖) := by
  have h := (EisensteinSeries.summable_norm_eisSummand (k := 3) (by decide)
    (UpperHalfPlane.mk z hz)).comp_injective
    (i := fun n : ℤ => ![1, n]) (by intro m n h; simpa using congrFun h 1)
  simpa [EisensteinSeries.eisSummand, Function.comp_def, one_div] using h

theorem cotangent_second_derivative_eq_tsum_cube {z : ℂ} (hz : 0 < z.im) :
    deriv (deriv (fun w : ℂ => Real.pi * Complex.cot (Real.pi * w))) z =
      2 * ∑' n : ℤ, 1 / (z + n) ^ 3 := by
  let f : ℤ → ℂ := fun n => 1 / (z + n) ^ 3
  have hf : Summable f := (summable_norm_one_div_int_add_cube hz).of_norm
  have hp := hf.comp_injective (i := fun n : ℕ => (n : ℤ)) Nat.cast_injective
  change Summable (fun n : ℕ => f (n : ℤ)) at hp
  have hm := hf.comp_injective (i := fun n : ℕ => -((n : ℤ) + 1))
    (by intro m n h; exact_mod_cast add_right_cancel (neg_injective h))
  change Summable (fun n : ℕ => f (-((n : ℤ) + 1))) at hm
  have hp' : Summable (fun n : ℕ => f (↑(n + 1))) :=
    (summable_nat_add_iff (f := fun n : ℕ => f (n : ℤ)) 1).mpr hp
  have hpair := hm.add hp'
  have hsplit : (∑' n : ℤ, f n) = f 0 + ∑' n : ℕ, (f (-((n : ℤ) + 1)) + f (↑(n + 1))) := by
    rw [tsum_of_nat_of_neg_add_one hp hm, hm.tsum_add hp']
    have hshift := hp.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one] at hshift
    linear_combination -hshift
  have hlim : Tendsto (fun N => cotangentSymmetricSum 2 N z) atTop (𝓝 (∑' n : ℤ, f n)) := by
    rw [hsplit]
    convert hpair.hasSum.tendsto_sum_nat.const_add (f 0) using 1
    ext N
    simp only [cotangentSymmetricSum, f, Int.cast_zero, add_zero,
      Int.cast_neg, Int.cast_add, Int.cast_one, Int.cast_natCast, Nat.cast_add,
      Nat.cast_one, sub_eq_add_neg]
  exact tendsto_nhds_unique (tendsto_cotangentSymmetricSum_cube hz) (hlim.const_mul 2)

end DirichletL

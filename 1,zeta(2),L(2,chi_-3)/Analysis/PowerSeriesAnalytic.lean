import Analysis.GeneratingFunctions

/-!
Complex analytic realizations of the rational formal ODE in CDT v2,
Lemma `defabc` and equation `zagr`. Convergence hypotheses are explicit.
-/

namespace DirichletL

open scoped ENNReal

/-- The complex multilinear series with the given rational formal coefficients. -/
noncomputable def complexSeries (p : PowerSeries ℚ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (PowerSeries.coeff (R := ℚ) n p : ℂ))

@[simp]
theorem coeff_complexSeries (p : PowerSeries ℚ) (n : ℕ) :
    (complexSeries p).coeff n = (PowerSeries.coeff (R := ℚ) n p : ℂ) := by
  simp [complexSeries]

/-- Formal differentiation agrees with complex differentiation on the expansion ball. -/
theorem hasFPowerSeriesOnBall_derivativeFun {f : ℂ → ℂ} {p : PowerSeries ℚ}
    {r : ℝ≥0∞} (h : HasFPowerSeriesOnBall f (complexSeries p) 0 r) :
    HasFPowerSeriesOnBall (deriv f) (complexSeries p.derivativeFun) 0 r := by
  let ev := ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)
  have heq : ev.compFormalMultilinearSeries (complexSeries p).derivSeries =
      complexSeries p.derivativeFun := by
    funext n
    apply ContinuousMultilinearMap.ext
    intro v
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      FormalMultilinearSeries.apply_eq_prod_smul_coeff]
    congr 1
    change (complexSeries p).derivSeries.coeff n 1 = _
    rw [FormalMultilinearSeries.derivSeries_coeff_one, coeff_complexSeries,
      coeff_complexSeries, PowerSeries.coeff_derivativeFun]
    simp [nsmul_eq_mul, mul_comm]
  simpa only [heq] using ev.comp_hasFPowerSeriesOnBall h.fderiv

theorem hasSum_of_hasFPowerSeriesOnBall {f : ℂ → ℂ} {p : PowerSeries ℚ}
    {r : ℝ≥0∞} (h : HasFPowerSeriesOnBall f (complexSeries p) 0 r)
    {z : ℂ} (hz : z ∈ EMetric.ball 0 r) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n p : ℂ) * z ^ n) (f z) := by
  simpa [complexSeries, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using h.hasSum hz

private theorem hasSum_X_pow_mul {p : PowerSeries ℚ} {z a : ℂ}
    (h : HasSum (fun n => (PowerSeries.coeff (R := ℚ) n p : ℂ) * z ^ n) a) (k : ℕ) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n (PowerSeries.X ^ k * p) : ℂ) * z ^ n)
      (z ^ k * a) := by
  apply (hasSum_nat_add_iff' k).mp
  have hzero : ∑ i ∈ Finset.range k,
      (PowerSeries.coeff (R := ℚ) i (PowerSeries.X ^ k * p) : ℂ) * z ^ i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [PowerSeries.coeff_X_pow_mul']
    simp [Nat.not_le.mpr (Finset.mem_range.mp hi)]
  rw [hzero, sub_zero]
  convert h.mul_left (z ^ k) using 1
  ext n
  rw [PowerSeries.coeff_X_pow_mul, pow_add]
  ring

private theorem hasSum_C_mul {p : PowerSeries ℚ} {z a : ℂ}
    (h : HasSum (fun n => (PowerSeries.coeff (R := ℚ) n p : ℂ) * z ^ n) a) (b : ℚ) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n (PowerSeries.C (R := ℚ) b * p) : ℂ) * z ^ n)
      ((b : ℂ) * a) := by
  simpa [PowerSeries.coeff_C_mul, mul_assoc] using h.mul_left (b : ℂ)

/-- Polynomial multiplication commutes with evaluation of a convergent scalar series. -/
theorem hasSum_polynomial_mul {p : PowerSeries ℚ} {z a : ℂ}
    (h : HasSum (fun n => (PowerSeries.coeff (R := ℚ) n p : ℂ) * z ^ n) a)
    (q : Polynomial ℚ) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n ((q : PowerSeries ℚ) * p) : ℂ) * z ^ n)
      (Polynomial.aeval z q * a) := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
    convert hq.add hr using 1
    · ext n
      simp only [Polynomial.coe_add, add_mul, map_add, Rat.cast_add]
    · simp only [map_add, add_mul]
  | monomial n b =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simpa only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X,
      map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, mul_assoc] using
      hasSum_C_mul (hasSum_X_pow_mul h n) b

/-- The constant formal series one sums to one at every complex point. -/
theorem hasSum_powerSeries_one (z : ℂ) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n (1 : PowerSeries ℚ) : ℂ) * z ^ n) 1 := by
  convert hasSum_ite_eq (0 : ℕ) (1 : ℂ) using 1
  ext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]

/-- Evaluation of the formal Zagier operator throughout an expansion ball. -/
theorem hasSum_generatingODE {f : ℂ → ℂ} {p : PowerSeries ℚ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (complexSeries p) 0 r)
    {z : ℂ} (hz : z ∈ EMetric.ball 0 r) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n (generatingODE p) : ℂ) * z ^ n)
      (z * (1 - z) * (1 - 9 * z) * deriv (deriv f) z +
        (1 - 20 * z + 27 * z ^ 2) * deriv f z + (9 * z - 3) * f z) := by
  have h0 := hasSum_of_hasFPowerSeriesOnBall hf hz
  have h1 := hasSum_of_hasFPowerSeriesOnBall (hasFPowerSeriesOnBall_derivativeFun hf) hz
  have h2 := hasSum_of_hasFPowerSeriesOnBall
    (hasFPowerSeriesOnBall_derivativeFun (hasFPowerSeriesOnBall_derivativeFun hf)) hz
  have hsum := (((((((hasSum_X_pow_mul h2 1).sub
    (hasSum_C_mul (hasSum_X_pow_mul h2 2) 10)).add
      (hasSum_C_mul (hasSum_X_pow_mul h2 3) 9)).add h1).sub
        (hasSum_C_mul (hasSum_X_pow_mul h1 1) 20)).add
          (hasSum_C_mul (hasSum_X_pow_mul h1 2) 27)).add
            (hasSum_C_mul (hasSum_X_pow_mul h0 1) 9)).sub (hasSum_C_mul h0 3)
  have hsum' : HasSum (fun n => (PowerSeries.coeff (R := ℚ) n (generatingODE p) : ℂ) * z ^ n)
      (z ^ 1 * deriv (deriv f) z - 10 * (z ^ 2 * deriv (deriv f) z) +
        9 * (z ^ 3 * deriv (deriv f) z) + deriv f z - 20 * (z ^ 1 * deriv f z) +
          27 * (z ^ 2 * deriv f z) + 9 * (z ^ 1 * f z) - 3 * f z) := by
    convert hsum using 1
    ext n
    simp only [generatingODE, map_sub, map_add, Rat.cast_sub, Rat.cast_add]
    ring
  convert hsum' using 1
  ring

/-- A convergent solution of the formal Zagier ODE satisfies its analytic ODE. -/
theorem generatingODE_eq_zero_of_hasFPowerSeriesOnBall {f : ℂ → ℂ}
    {p : PowerSeries ℚ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (complexSeries p) 0 r)
    (hp : generatingODE p = 0) {z : ℂ} (hz : z ∈ EMetric.ball 0 r) :
    z * (1 - z) * (1 - 9 * z) * deriv (deriv f) z +
        (1 - 20 * z + 27 * z ^ 2) * deriv f z + (9 * z - 3) * f z = 0 := by
  have hs := hasSum_generatingODE hf hz
  have hzero : HasSum
      (fun n => (PowerSeries.coeff (R := ℚ) n (generatingODE p) : ℂ) * z ^ n) 0 := by
    simpa only [hp, map_zero, Rat.cast_zero, zero_mul] using
      (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  exact hs.unique hzero

end DirichletL

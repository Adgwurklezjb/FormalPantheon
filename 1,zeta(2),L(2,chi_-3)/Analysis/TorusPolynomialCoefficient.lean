import Analysis.TorusCauchyCoefficient
import Analysis.ComplexPowerSeriesEvaluation

/-!
The polynomial multiplier in CDT v2's Cauchy integral, supplied TeX 4092-4137.
Meanings, the Fourier sign, and empty-type checks precede these proofs in
-/

namespace DirichletL

open MeasureTheory
open scoped Classical

attribute [local instance] fact_two_pi_pos

theorem integrable_polynomial_separate_torus_kernel {ι σ : Type*}
    [Fintype ι] [Fintype σ] (W : MvPolynomial σ ℂ) (a : ι → ℂ)
    {f : ι → σ → ℂ → ℂ}
    (hd : ∀ i j, DifferentiableOn ℂ (f i j) (Metric.closedBall 0 1)) (n : σ →₀ ℕ) :
    Integrable (fun t : σ → AddCircle (2 * Real.pi) =>
      (MvPolynomial.eval (fun j => fourier 1 (t j)) W *
        (∑ i, a i * ∏ j, f i j (fourier 1 (t j)))) *
          ∏ j, fourier (-(n j : ℤ)) (t j))
      (Measure.pi (fun _ : σ => AddCircle.haarAddCircle)) := by
  have hz : Continuous (fun t : σ → AddCircle (2 * Real.pi) =>
      fun j => fourier 1 (t j)) :=
    continuous_pi (fun j => (fourier 1).continuous.comp (continuous_apply j))
  have hF : Continuous (fun t : σ → AddCircle (2 * Real.pi) =>
      ∑ i, a i * ∏ j, f i j (fourier 1 (t j))) := by
    apply continuous_finset_sum Finset.univ
    intro i hi
    exact continuous_const.mul (continuous_separate_torus_product (hd i))
  have hk : Continuous (fun t : σ → AddCircle (2 * Real.pi) =>
      ∏ j, fourier (-(n j : ℤ)) (t j)) := by
    apply continuous_finset_prod Finset.univ
    intro j hj
    exact (fourier (-(n j : ℤ))).continuous.comp (continuous_apply j)
  have hc := ((W.continuous_eval.comp hz).mul hF).mul hk
  simpa only [integrableOn_univ] using
    hc.continuousOn.integrableOn_compact
      (μ := Measure.pi (fun _ : σ => AddCircle.haarAddCircle)) isCompact_univ

theorem coeff_polynomial_mul_sum_separate_eq_torusIntegral {ι σ : Type*}
    [Fintype ι] [Fintype σ] (W : MvPolynomial σ ℂ) (a : ι → ℂ)
    (p : ι → σ → PowerSeries ℂ) (f : ι → σ → ℂ → ℂ)
    (hf : ∀ i j, HasFPowerSeriesAt (f i j)
      (FormalMultilinearSeries.ofScalars ℂ (fun k => PowerSeries.coeff (R := ℂ) k (p i j))) 0)
    (hd : ∀ i j, DifferentiableOn ℂ (f i j) (Metric.closedBall 0 1)) (n : σ →₀ ℕ) :
    MvPowerSeries.coeff (R := ℂ) n ((W : MvPowerSeries σ ℂ) *
      ∑ i, MvPowerSeries.C (σ := σ) (R := ℂ) (a i) * ∏ j, powerSeriesInVariable ℂ j (p i j)) =
      ∫ t : σ → AddCircle (2 * Real.pi),
        (MvPolynomial.eval (fun j => fourier 1 (t j)) W *
          (∑ i, a i * ∏ j, f i j (fourier 1 (t j)))) *
            ∏ j, fourier (-(n j : ℤ)) (t j)
        ∂Measure.pi (fun _ : σ => AddCircle.haarAddCircle) := by
  induction W using MvPolynomial.induction_on' with
  | add W V hW hV =>
    simp only [MvPolynomial.coe_add, add_mul, map_add]
    rw [integral_add (integrable_polynomial_separate_torus_kernel W a hd n)
      (integrable_polynomial_separate_torus_kernel V a hd n), hW, hV]
  | monomial e b =>
    have hshift : ∀ i j, HasFPowerSeriesAt (fun z => z ^ e j * f i j z)
        (FormalMultilinearSeries.ofScalars ℂ
          (fun k => PowerSeries.coeff (R := ℂ) k (PowerSeries.X ^ e j * p i j))) 0 :=
      fun i j => hasFPowerSeriesAt_complexPowerSeries_X_pow_mul (hf i j) (e j)
    have hdshift : ∀ i j, DifferentiableOn ℂ (fun z => z ^ e j * f i j z)
        (Metric.closedBall 0 1) := fun i j =>
      ((differentiable_id.pow (e j)).differentiableOn).mul (hd i j)
    have h := coeff_sum_separate_eq_torusIntegral (fun i => b * a i)
      (fun i j => PowerSeries.X ^ e j * p i j) (fun i j z => z ^ e j * f i j z)
      hshift hdshift n
    have he : Finsupp.equivFunOnFinite.symm (fun j => e j) = e := by
      ext j
      rfl
    have hm : MvPowerSeries.monomial (R := ℂ) e b =
        MvPowerSeries.C (σ := σ) (R := ℂ) b * MvPowerSeries.monomial (R := ℂ) e 1 := by
      simpa only [zero_add, mul_one] using
        (MvPowerSeries.monomial_mul_monomial (0 : σ →₀ ℕ) e b (1 : ℂ)).symm
    have hformal : (∑ i, MvPowerSeries.C (σ := σ) (R := ℂ) (b * a i) *
        ∏ j, powerSeriesInVariable ℂ j (PowerSeries.X ^ e j * p i j)) =
        (MvPolynomial.monomial e b : MvPowerSeries σ ℂ) *
          ∑ i, MvPowerSeries.C (σ := σ) (R := ℂ) (a i) * ∏ j, powerSeriesInVariable ℂ j (p i j) := by
      rw [MvPolynomial.coe_monomial, hm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [PowerSeries.X_pow_eq]
      rw [prod_powerSeriesInVariable_shift, he, map_mul]
      ring
    rw [hformal] at h
    rw [h]
    apply integral_congr_ae
    filter_upwards with t
    congr 1
    rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [Finset.prod_mul_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem norm_coeff_polynomial_mul_sum_separate_le_integral {ι σ : Type*}
    [Fintype ι] [Fintype σ] (W : MvPolynomial σ ℂ) (a : ι → ℂ)
    (p : ι → σ → PowerSeries ℂ) (f : ι → σ → ℂ → ℂ)
    (hf : ∀ i j, HasFPowerSeriesAt (f i j)
      (FormalMultilinearSeries.ofScalars ℂ (fun k => PowerSeries.coeff (R := ℂ) k (p i j))) 0)
    (hd : ∀ i j, DifferentiableOn ℂ (f i j) (Metric.closedBall 0 1)) (n : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff (R := ℂ) n ((W : MvPowerSeries σ ℂ) *
      ∑ i, MvPowerSeries.C (σ := σ) (R := ℂ) (a i) * ∏ j, powerSeriesInVariable ℂ j (p i j))‖ ≤
      ∫ t : σ → AddCircle (2 * Real.pi),
        ‖MvPolynomial.eval (fun j => fourier 1 (t j)) W *
          (∑ i, a i * ∏ j, f i j (fourier 1 (t j)))‖
        ∂Measure.pi (fun _ : σ => AddCircle.haarAddCircle) := by
  rw [coeff_polynomial_mul_sum_separate_eq_torusIntegral W a p f hf hd n]
  simpa only [norm_mul, norm_prod_fourier, mul_one] using
    norm_integral_le_integral_norm
      (μ := Measure.pi (fun _ : σ => AddCircle.haarAddCircle))
      (fun t : σ → AddCircle (2 * Real.pi) =>
        (MvPolynomial.eval (fun j => fourier 1 (t j)) W *
          (∑ i, a i * ∏ j, f i j (fourier 1 (t j)))) *
            ∏ j, fourier (-(n j : ℤ)) (t j))

theorem norm_coeff_polynomial_mul_sum_separate_le_of_bound {ι σ : Type*}
    [Fintype ι] [Fintype σ] (W : MvPolynomial σ ℂ) (a : ι → ℂ)
    (p : ι → σ → PowerSeries ℂ) (f : ι → σ → ℂ → ℂ)
    (hf : ∀ i j, HasFPowerSeriesAt (f i j)
      (FormalMultilinearSeries.ofScalars ℂ (fun k => PowerSeries.coeff (R := ℂ) k (p i j))) 0)
    (hd : ∀ i j, DifferentiableOn ℂ (f i j) (Metric.closedBall 0 1))
    (n : σ →₀ ℕ) (C : ℝ)
    (hC : ∀ t : σ → AddCircle (2 * Real.pi),
      ‖MvPolynomial.eval (fun j => fourier 1 (t j)) W *
        (∑ i, a i * ∏ j, f i j (fourier 1 (t j)))‖ ≤ C) :
    ‖MvPowerSeries.coeff (R := ℂ) n ((W : MvPowerSeries σ ℂ) *
      ∑ i, MvPowerSeries.C (σ := σ) (R := ℂ) (a i) * ∏ j, powerSeriesInVariable ℂ j (p i j))‖ ≤ C := by
  rw [coeff_polynomial_mul_sum_separate_eq_torusIntegral W a p f hf hd n]
  have hb : ∀ᵐ t : σ → AddCircle (2 * Real.pi)
      ∂Measure.pi (fun _ : σ => AddCircle.haarAddCircle),
      ‖(MvPolynomial.eval (fun j => fourier 1 (t j)) W *
        (∑ i, a i * ∏ j, f i j (fourier 1 (t j)))) *
          ∏ j, fourier (-(n j : ℤ)) (t j)‖ ≤ C :=
    Filter.Eventually.of_forall (fun t => by
      simpa only [norm_mul, norm_prod_fourier, mul_one] using hC t)
  simpa using norm_integral_le_of_norm_le_const hb

end DirichletL

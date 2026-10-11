import Analysis.UnitCircleCoefficient
import Analysis.PowerSeriesCoordinates

/-!
The coefficient integral for finite separated expressions in CDT v2,
supplied TeX 3965-3998 and 4092-4130. The measure is the product of normalized
circle Haar measures. Meanings and edge cases precede these proofs in
-/

namespace DirichletL

open MeasureTheory
open scoped Classical

attribute [local instance] fact_two_pi_pos

theorem continuous_fourier_boundary {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 1)) :
    Continuous (fun t : AddCircle (2 * Real.pi) => f (fourier 1 t)) := by
  apply hd.continuousOn.comp_continuous (fourier 1).continuous
  intro t
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_eq (Circle.norm_coe _)

theorem norm_prod_fourier {σ : Type*} [Fintype σ] {T : ℝ}
    (n : σ → ℤ) (t : σ → AddCircle T) :
    ‖∏ j, fourier (n j) (t j)‖ = 1 := by
  rw [norm_prod]
  have h (j : σ) : ‖fourier (n j) (t j)‖ = 1 := Circle.norm_coe _
  simp only [h, Finset.prod_const_one]

theorem continuous_separate_torus_product {σ : Type*} [Fintype σ]
    {f : σ → ℂ → ℂ} (hd : ∀ j, DifferentiableOn ℂ (f j) (Metric.closedBall 0 1)) :
    Continuous (fun t : σ → AddCircle (2 * Real.pi) => ∏ j, f j (fourier 1 (t j))) := by
  apply continuous_finset_prod Finset.univ
  intro j hj
  exact (continuous_fourier_boundary (hd j)).comp (continuous_apply j)

theorem integrable_separate_torus_kernel {σ : Type*} [Fintype σ]
    {f : σ → ℂ → ℂ} (hd : ∀ j, DifferentiableOn ℂ (f j) (Metric.closedBall 0 1))
    (n : σ →₀ ℕ) :
    Integrable (fun t : σ → AddCircle (2 * Real.pi) =>
      (∏ j, f j (fourier 1 (t j))) * ∏ j, fourier (-(n j : ℤ)) (t j))
      (Measure.pi (fun _ : σ => AddCircle.haarAddCircle)) := by
  have hk : Continuous (fun t : σ → AddCircle (2 * Real.pi) =>
      ∏ j, fourier (-(n j : ℤ)) (t j)) := by
    apply continuous_finset_prod Finset.univ
    intro j hj
    exact (fourier (-(n j : ℤ))).continuous.comp (continuous_apply j)
  have hc := (continuous_separate_torus_product hd).mul hk
  simpa only [integrableOn_univ] using
    hc.continuousOn.integrableOn_compact
      (μ := Measure.pi (fun _ : σ => AddCircle.haarAddCircle)) isCompact_univ

theorem coeff_prod_separate_eq_torusIntegral {σ : Type*} [Fintype σ]
    (p : σ → PowerSeries ℂ) (f : σ → ℂ → ℂ)
    (hf : ∀ j, HasFPowerSeriesAt (f j)
      (FormalMultilinearSeries.ofScalars ℂ (fun k => PowerSeries.coeff (R := ℂ) k (p j))) 0)
    (hd : ∀ j, DifferentiableOn ℂ (f j) (Metric.closedBall 0 1)) (n : σ →₀ ℕ) :
    MvPowerSeries.coeff (R := ℂ) n (∏ j, powerSeriesInVariable ℂ j (p j)) =
      ∫ t : σ → AddCircle (2 * Real.pi),
        (∏ j, f j (fourier 1 (t j))) * ∏ j, fourier (-(n j : ℤ)) (t j)
        ∂Measure.pi (fun _ : σ => AddCircle.haarAddCircle) := by
  rw [coeff_prod_powerSeriesInVariable]
  calc
    (∏ j, PowerSeries.coeff (R := ℂ) (n j) (p j)) =
        ∏ j, ∫ t : AddCircle (2 * Real.pi),
          fourier (-(n j : ℤ)) t * f j (fourier 1 t) ∂AddCircle.haarAddCircle := by
      apply Finset.prod_congr rfl
      intro j hj
      exact coeff_eq_fourierCoeff_unitCircle (hf j) (hd j) (n j)
    _ = ∫ t : σ → AddCircle (2 * Real.pi),
        ∏ j, fourier (-(n j : ℤ)) (t j) * f j (fourier 1 (t j))
        ∂Measure.pi (fun _ : σ => AddCircle.haarAddCircle) := by
      exact (integral_fintype_prod_eq_prod
        (μ := fun _ : σ => AddCircle.haarAddCircle)
        (fun j (t : AddCircle (2 * Real.pi)) =>
          fourier (-(n j : ℤ)) t * f j (fourier 1 t))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [Finset.prod_mul_distrib, mul_comm]

theorem coeff_sum_separate_eq_torusIntegral {ι σ : Type*} [Fintype ι] [Fintype σ]
    (a : ι → ℂ) (p : ι → σ → PowerSeries ℂ) (f : ι → σ → ℂ → ℂ)
    (hf : ∀ i j, HasFPowerSeriesAt (f i j)
      (FormalMultilinearSeries.ofScalars ℂ (fun k => PowerSeries.coeff (R := ℂ) k (p i j))) 0)
    (hd : ∀ i j, DifferentiableOn ℂ (f i j) (Metric.closedBall 0 1)) (n : σ →₀ ℕ) :
    MvPowerSeries.coeff (R := ℂ) n
        (∑ i, MvPowerSeries.C (σ := σ) (R := ℂ) (a i) * ∏ j, powerSeriesInVariable ℂ j (p i j)) =
      ∫ t : σ → AddCircle (2 * Real.pi),
        (∑ i, a i * ∏ j, f i j (fourier 1 (t j))) * ∏ j, fourier (-(n j : ℤ)) (t j)
        ∂Measure.pi (fun _ : σ => AddCircle.haarAddCircle) := by
  simp only [map_sum, MvPowerSeries.coeff_C_mul]
  calc
    (∑ i, a i * MvPowerSeries.coeff (R := ℂ) n (∏ j, powerSeriesInVariable ℂ j (p i j))) =
        ∑ i, a i * ∫ t : σ → AddCircle (2 * Real.pi),
          (∏ j, f i j (fourier 1 (t j))) * ∏ j, fourier (-(n j : ℤ)) (t j)
          ∂Measure.pi (fun _ : σ => AddCircle.haarAddCircle) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [coeff_prod_separate_eq_torusIntegral (p i) (f i) (hf i) (hd i) n]
    _ = ∫ t : σ → AddCircle (2 * Real.pi),
        ∑ i, a i * ((∏ j, f i j (fourier 1 (t j))) *
          ∏ j, fourier (-(n j : ℤ)) (t j))
        ∂Measure.pi (fun _ : σ => AddCircle.haarAddCircle) := by
      rw [integral_finset_sum Finset.univ
        (fun i _ => (integrable_separate_torus_kernel (hd i) n).const_mul (a i))]
      simp only [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [Finset.sum_mul, mul_assoc]

theorem norm_coeff_sum_separate_le_integral {ι σ : Type*} [Fintype ι] [Fintype σ]
    (a : ι → ℂ) (p : ι → σ → PowerSeries ℂ) (f : ι → σ → ℂ → ℂ)
    (hf : ∀ i j, HasFPowerSeriesAt (f i j)
      (FormalMultilinearSeries.ofScalars ℂ (fun k => PowerSeries.coeff (R := ℂ) k (p i j))) 0)
    (hd : ∀ i j, DifferentiableOn ℂ (f i j) (Metric.closedBall 0 1)) (n : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff (R := ℂ) n
        (∑ i, MvPowerSeries.C (σ := σ) (R := ℂ) (a i) * ∏ j, powerSeriesInVariable ℂ j (p i j))‖ ≤
      ∫ t : σ → AddCircle (2 * Real.pi), ‖∑ i, a i * ∏ j, f i j (fourier 1 (t j))‖
        ∂Measure.pi (fun _ : σ => AddCircle.haarAddCircle) := by
  rw [coeff_sum_separate_eq_torusIntegral a p f hf hd n]
  simpa only [norm_mul, norm_prod_fourier, mul_one] using
    norm_integral_le_integral_norm
      (μ := Measure.pi (fun _ : σ => AddCircle.haarAddCircle))
      (fun t : σ → AddCircle (2 * Real.pi) =>
        (∑ i, a i * ∏ j, f i j (fourier 1 (t j))) * ∏ j, fourier (-(n j : ℤ)) (t j))

theorem norm_coeff_sum_separate_le_of_bound {ι σ : Type*} [Fintype ι] [Fintype σ]
    (a : ι → ℂ) (p : ι → σ → PowerSeries ℂ) (f : ι → σ → ℂ → ℂ)
    (hf : ∀ i j, HasFPowerSeriesAt (f i j)
      (FormalMultilinearSeries.ofScalars ℂ (fun k => PowerSeries.coeff (R := ℂ) k (p i j))) 0)
    (hd : ∀ i j, DifferentiableOn ℂ (f i j) (Metric.closedBall 0 1))
    (n : σ →₀ ℕ) (C : ℝ)
    (hC : ∀ t : σ → AddCircle (2 * Real.pi),
      ‖∑ i, a i * ∏ j, f i j (fourier 1 (t j))‖ ≤ C) :
    ‖MvPowerSeries.coeff (R := ℂ) n
      (∑ i, MvPowerSeries.C (σ := σ) (R := ℂ) (a i) * ∏ j, powerSeriesInVariable ℂ j (p i j))‖ ≤ C := by
  rw [coeff_sum_separate_eq_torusIntegral a p f hf hd n]
  have hb : ∀ᵐ t : σ → AddCircle (2 * Real.pi)
      ∂Measure.pi (fun _ : σ => AddCircle.haarAddCircle),
      ‖(∑ i, a i * ∏ j, f i j (fourier 1 (t j))) *
        ∏ j, fourier (-(n j : ℤ)) (t j)‖ ≤ C :=
    Filter.Eventually.of_forall (fun t => by
      simpa only [norm_mul, norm_prod_fourier, mul_one] using hC t)
  simpa using norm_integral_le_of_norm_le_const hb

end DirichletL

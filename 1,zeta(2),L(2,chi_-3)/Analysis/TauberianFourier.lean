import Analysis.TauberianWeightedSums

/-!
Fourier estimates for CDT v2's lcm asymptotic route (supplied TeX
3291-3310). Based on the PrimeNumberTheoremAnd contributors,
Wiener.lean at revision 0766218b21b11ddf24103352ece7f0cb730945e0,
lines 387-399 and 1478-1545. The original source and Apache 2.0 license
canonical Schwartz space and its derivative and Fourier linear maps.
-/

namespace DirichletL

open MeasureTheory Filter Set
open scoped Topology FourierTransform SchwartzMap

/-- The weighted L1 size that controls the quadratic Fourier decay. -/
noncomputable def tauberianFourierSize (ψ : 𝓢(ℝ, ℂ)) : ℝ :=
  (∫ t, ‖ψ t‖) + (4 * Real.pi ^ 2)⁻¹ *
    ∫ t, ‖SchwartzMap.derivCLM ℂ (SchwartzMap.derivCLM ℂ ψ) t‖

theorem tauberianFourierSize_nonneg (ψ : 𝓢(ℝ, ℂ)) : 0 ≤ tauberianFourierSize ψ := by
  unfold tauberianFourierSize
  exact add_nonneg (integral_nonneg (fun _ => norm_nonneg _))
    (mul_nonneg (by positivity) (integral_nonneg (fun _ => norm_nonneg _)))

theorem fourier_sub_second_deriv (ψ : 𝓢(ℝ, ℂ)) (u : ℝ) :
    𝓕 (ψ - ((4 : ℂ) * (Real.pi : ℂ) ^ 2)⁻¹ •
      SchwartzMap.derivCLM ℂ (SchwartzMap.derivCLM ℂ ψ)) u =
      ((1 : ℂ) + (u : ℂ) ^ 2) * 𝓕 ψ u := by
  have h1 : 𝓕 (SchwartzMap.derivCLM ℂ ψ) u =
      (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ)) * 𝓕 ψ u := by
    simpa only [smul_eq_mul] using congrFun
      (Real.fourierIntegral_deriv ψ.integrable ψ.differentiable
        (SchwartzMap.derivCLM ℂ ψ).integrable) u
  have h2 : 𝓕 (SchwartzMap.derivCLM ℂ (SchwartzMap.derivCLM ℂ ψ)) u =
      (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ)) * 𝓕 (SchwartzMap.derivCLM ℂ ψ) u := by
    simpa only [smul_eq_mul] using congrFun
      (Real.fourierIntegral_deriv (SchwartzMap.derivCLM ℂ ψ).integrable
        (SchwartzMap.derivCLM ℂ ψ).differentiable
        (SchwartzMap.derivCLM ℂ (SchwartzMap.derivCLM ℂ ψ)).integrable) u
  change (SchwartzMap.fourierTransformCLM ℂ (ψ - ((4 : ℂ) * (Real.pi : ℂ) ^ 2)⁻¹ •
    SchwartzMap.derivCLM ℂ (SchwartzMap.derivCLM ℂ ψ))) u = _
  rw [map_sub, map_smul]
  change 𝓕 ψ u - ((4 : ℂ) * (Real.pi : ℂ) ^ 2)⁻¹ *
    𝓕 (SchwartzMap.derivCLM ℂ (SchwartzMap.derivCLM ℂ ψ)) u = _
  rw [h2, h1]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hp]
  ring_nf
  simp

theorem norm_fourier_le_tauberianFourierSize (ψ : 𝓢(ℝ, ℂ)) (u : ℝ) :
    ‖𝓕 ψ u‖ ≤ tauberianFourierSize ψ * (1 + u ^ 2)⁻¹ := by
  have hu : 0 < 1 + u ^ 2 := by positivity
  have hfactor : ‖(1 : ℂ) + (u : ℂ) ^ 2‖ = 1 + u ^ 2 := by
    norm_cast
    rw [Real.norm_eq_abs, abs_of_nonneg hu.le]
  have hcoef : ‖((4 : ℂ) * (Real.pi : ℂ) ^ 2)⁻¹‖ = (4 * Real.pi ^ 2)⁻¹ := by simp
  rw [← div_eq_mul_inv, le_div_iff₀ hu, mul_comm, ← hfactor, ← norm_mul,
    ← fourier_sub_second_deriv]
  change ‖(SchwartzMap.fourierTransformCLM ℂ
    (ψ - ((4 : ℂ) * (Real.pi : ℂ) ^ 2)⁻¹ •
      SchwartzMap.derivCLM ℂ (SchwartzMap.derivCLM ℂ ψ))) u‖ ≤ _
  rw [map_sub, map_smul]
  change ‖𝓕 ψ u - ((4 : ℂ) * (Real.pi : ℂ) ^ 2)⁻¹ *
    𝓕 (SchwartzMap.derivCLM ℂ (SchwartzMap.derivCLM ℂ ψ)) u‖ ≤ _
  apply (norm_sub_le _ _).trans
  rw [norm_mul, hcoef]
  unfold tauberianFourierSize
  exact add_le_add (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _)
    (mul_le_mul_of_nonneg_left
      (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _) (by positivity))

/-- The logarithmically sampled Fourier term, including its zero-index convention. -/
noncomputable def tauberianFourierTerm (f : ℕ → ℂ) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) (n : ℕ) : ℂ :=
  (f n / (n : ℂ)) * 𝓕 ψ (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x))

theorem tauberianFourierTerm_zero (f : ℕ → ℂ) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    tauberianFourierTerm f ψ x 0 = 0 := by
  simp [tauberianFourierTerm]

theorem norm_tauberianFourierTerm_le (f : ℕ → ℂ) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) (n : ℕ) :
    ‖tauberianFourierTerm f ψ x n‖ ≤
      tauberianFourierSize ψ * (‖f n‖ * tauberianWeight x n) := by
  by_cases hn : n = 0
  · simp [hn, tauberianFourierTerm_zero, tauberianWeight_zero]
  calc
    ‖tauberianFourierTerm f ψ x n‖ = (‖f n‖ / (n : ℝ)) *
        ‖𝓕 ψ (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x))‖ := by
      simp only [tauberianFourierTerm, norm_mul, norm_div, Complex.norm_natCast]
    _ ≤ (‖f n‖ / (n : ℝ)) * (tauberianFourierSize ψ *
        (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x)) ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left (norm_fourier_le_tauberianFourierSize ψ _) (by positivity)
    _ = _ := by
      unfold tauberianWeight
      rw [div_eq_mul_inv]
      ring

theorem summable_norm_tauberianFourierTerm {f : ℕ → ℂ} {C : ℝ}
    (hsum : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ C * n) {x : ℝ} (hx : 0 < x)
    (ψ : 𝓢(ℝ, ℂ)) : Summable (fun n => ‖tauberianFourierTerm f ψ x n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_tauberianFourierTerm_le f ψ x)
    ((summable_norm_mul_tauberianWeight hsum hx).mul_left (tauberianFourierSize ψ))

theorem norm_tsum_tauberianFourierTerm_le {f : ℕ → ℂ} {C : ℝ}
    (hsum : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ C * n) {x : ℝ} (hx : 0 < x)
    (ψ : 𝓢(ℝ, ℂ)) :
    ‖∑' n, tauberianFourierTerm f ψ x n‖ ≤ tauberianFourierSize ψ * C * (1 + 2 * Real.pi ^ 2) := by
  have hs := summable_norm_tauberianFourierTerm hsum hx ψ
  have hw := (summable_norm_mul_tauberianWeight hsum hx).mul_left (tauberianFourierSize ψ)
  calc
    ‖∑' n, tauberianFourierTerm f ψ x n‖ ≤ ∑' n, ‖tauberianFourierTerm f ψ x n‖ :=
      norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n, tauberianFourierSize ψ * (‖f n‖ * tauberianWeight x n) :=
      Summable.tsum_mono hs hw (norm_tauberianFourierTerm_le f ψ x)
    _ = tauberianFourierSize ψ * ∑' n, ‖f n‖ * tauberianWeight x n := by rw [tsum_mul_left]
    _ ≤ tauberianFourierSize ψ * (C * (1 + 2 * Real.pi ^ 2)) :=
      mul_le_mul_of_nonneg_left (tsum_norm_mul_tauberianWeight_le hsum hx)
        (tauberianFourierSize_nonneg ψ)
    _ = _ := by ring

theorem norm_setIntegral_fourier_div_le (ψ : 𝓢(ℝ, ℂ)) (a : ℝ) :
    ‖∫ u in Ici a, 𝓕 ψ (u / (2 * Real.pi))‖ ≤ tauberianFourierSize ψ * (2 * Real.pi ^ 2) := by
  have hf : Integrable (fun u : ℝ => 𝓕 ψ (u / (2 * Real.pi))) :=
    (SchwartzMap.fourierTransformCLM ℂ ψ).integrable.comp_div (by positivity)
  have hg : Integrable (fun u : ℝ => (1 + (u / (2 * Real.pi)) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div (by positivity)
  calc
    ‖∫ u in Ici a, 𝓕 ψ (u / (2 * Real.pi))‖ ≤
        ∫ u in Ici a, ‖𝓕 ψ (u / (2 * Real.pi))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ici a, tauberianFourierSize ψ * (1 + (u / (2 * Real.pi)) ^ 2)⁻¹ :=
      setIntegral_mono hf.norm.integrableOn (hg.const_mul _).integrableOn
        (fun u => norm_fourier_le_tauberianFourierSize ψ _)
    _ ≤ ∫ u : ℝ, tauberianFourierSize ψ * (1 + (u / (2 * Real.pi)) ^ 2)⁻¹ :=
      setIntegral_le_integral (hg.const_mul _) (Eventually.of_forall
        (fun u => mul_nonneg (tauberianFourierSize_nonneg ψ) (by positivity)))
    _ = _ := by
      rw [integral_const_mul, Measure.integral_comp_div (fun u : ℝ => (1 + u ^ 2)⁻¹)
        (2 * Real.pi)]
      simp only [abs_of_pos Real.two_pi_pos, integral_univ_inv_one_add_sq, smul_eq_mul]
      ring

theorem norm_tauberian_residual_le {f : ℕ → ℂ} {C : ℝ}
    (hsum : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ C * n) {x : ℝ} (hx : 0 < x)
    (ψ : 𝓢(ℝ, ℂ)) (A : ℂ) :
    ‖(∑' n, tauberianFourierTerm f ψ x n) -
        A * ∫ u in Ici (-Real.log x), 𝓕 ψ (u / (2 * Real.pi))‖ ≤
      tauberianFourierSize ψ * (C * (1 + 2 * Real.pi ^ 2) + ‖A‖ * (2 * Real.pi ^ 2)) := by
  have h1 := norm_tsum_tauberianFourierTerm_le hsum hx ψ
  have h2 := mul_le_mul_of_nonneg_left
    (norm_setIntegral_fourier_div_le ψ (-Real.log x)) (norm_nonneg A)
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  convert add_le_add h1 h2 using 1
  ring

end DirichletL

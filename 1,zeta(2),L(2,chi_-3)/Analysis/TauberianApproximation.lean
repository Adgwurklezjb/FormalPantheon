import Analysis.SchwartzCutoff
import Analysis.TauberianFourier

/-!
Compact approximation for the Fourier size used in the Wiener-Ikehara
argument for CDT v2 Section 2.2 (supplied TeX 3291-3310). The cutoff
strategy appears in PNT+ Wiener.lean, revision
0766218b21b11ddf24103352ece7f0cb730945e0, lines 1545-1636, archived with
This proof uses the native Schwartz space and dominated convergence.
-/

namespace DirichletL

open MeasureTheory Filter Set
open scoped Topology SchwartzMap ContDiff

theorem tendsto_tauberianFourierSize_sub_schwartzCutoff (ψ χ : 𝓢(ℝ, ℂ))
    (hχ : HasCompactSupport (χ : ℝ → ℂ)) (hχ0 : χ 0 = 1) :
    Tendsto (fun N : ℕ => tauberianFourierSize
      (ψ - schwartzCutoff ψ χ hχ ((N : ℝ) + 1) (by positivity))) atTop (𝓝 0) := by
  let D : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℂ
  let φ (N : ℕ) := schwartzCutoff ψ χ hχ ((N : ℝ) + 1) (by positivity)
  let F (N : ℕ) := ψ - φ N
  let M0 := SchwartzMap.seminorm ℂ 0 0 χ
  let M1 := SchwartzMap.seminorm ℂ 0 0 (D χ)
  let M2 := SchwartzMap.seminorm ℂ 0 0 (D (D χ))
  have hM0 (t : ℝ) : ‖χ t‖ ≤ M0 := SchwartzMap.norm_le_seminorm ℂ χ t
  have hM1 (t : ℝ) : ‖D χ t‖ ≤ M1 := SchwartzMap.norm_le_seminorm ℂ (D χ) t
  have hM2 (t : ℝ) : ‖D (D χ) t‖ ≤ M2 := SchwartzMap.norm_le_seminorm ℂ (D (D χ)) t
  have ha (N : ℕ) : ‖(Complex.ofReal ((N : ℝ) + 1))⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by simp)
  have hi : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hiC : Tendsto (fun N : ℕ => (Complex.ofReal ((N : ℝ) + 1))⁻¹) atTop (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).comp hi
  have ht (t : ℝ) : Tendsto (fun N : ℕ => t / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul t
  have hlim0 (t : ℝ) : Tendsto (fun N => F N t) atTop (𝓝 0) := by
    have hc := (χ.continuous.tendsto 0).comp (ht t)
    change Tendsto (fun N : ℕ => ψ t - ψ t * χ (t / ((N : ℝ) + 1))) atTop (𝓝 0)
    simpa only [Function.comp_def, hχ0, mul_one, sub_self] using
      (hc.const_mul (ψ t)).const_sub (ψ t)
  have hlim2 (t : ℝ) : Tendsto (fun N => D (D (F N)) t) atTop (𝓝 0) := by
    have hc0 := (χ.continuous.tendsto 0).comp (ht t)
    have hc1 := ((D χ).continuous.tendsto 0).comp (ht t)
    have hc2 := ((D (D χ)).continuous.tendsto 0).comp (ht t)
    have hp : Tendsto (fun N => D (D (φ N)) t) atTop (𝓝 (D (D ψ) t)) := by
      simp only [D, φ, deriv_deriv_schwartzCutoff]
      simpa only [Function.comp_def, hχ0, mul_one, mul_zero, zero_mul, add_zero,
        zero_pow (by norm_num : 2 ≠ 0)]
        using ((hc0.const_mul (D (D ψ) t)).add
          (((hiC.const_mul 2).mul_const (D ψ t)).mul hc1)).add
            (((hiC.pow 2).mul_const (ψ t)).mul hc2)
    simpa only [F, map_sub, SchwartzMap.sub_apply, sub_self] using hp.const_sub (D (D ψ) t)
  have hb0 (N : ℕ) (t : ℝ) : ‖F N t‖ ≤ (1 + M0) * ‖ψ t‖ := by
    change ‖ψ t - ψ t * χ (t / ((N : ℝ) + 1))‖ ≤ _
    calc
      _ ≤ ‖ψ t‖ + ‖ψ t‖ * ‖χ (t / ((N : ℝ) + 1))‖ := by
        simpa only [norm_mul] using norm_sub_le (ψ t) (ψ t * χ (t / ((N : ℝ) + 1)))
      _ ≤ _ := by nlinarith [hM0 (t / ((N : ℝ) + 1)), norm_nonneg (ψ t)]
  have hb2 (N : ℕ) (t : ℝ) : ‖D (D (F N)) t‖ ≤
      (1 + M0) * ‖D (D ψ) t‖ + 2 * M1 * ‖D ψ t‖ + M2 * ‖ψ t‖ := by
    have hp : ‖D (D (φ N)) t‖ ≤
        M0 * ‖D (D ψ) t‖ + 2 * M1 * ‖D ψ t‖ + M2 * ‖ψ t‖ := by
      simp only [D, φ, deriv_deriv_schwartzCutoff]
      calc
        _ ≤ ‖SchwartzMap.derivCLM ℂ (SchwartzMap.derivCLM ℂ ψ) t * χ (t / ((N : ℝ) + 1))‖ +
            ‖2 * (Complex.ofReal ((N : ℝ) + 1))⁻¹ * SchwartzMap.derivCLM ℂ ψ t *
              SchwartzMap.derivCLM ℂ χ (t / ((N : ℝ) + 1))‖ +
            ‖((Complex.ofReal ((N : ℝ) + 1))⁻¹) ^ 2 * ψ t *
              SchwartzMap.derivCLM ℂ (SchwartzMap.derivCLM ℂ χ) (t / ((N : ℝ) + 1))‖ :=
          (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
        _ ≤ _ := by
          simp only [norm_mul, norm_pow, Complex.norm_ofNat]
          calc
            _ ≤ ‖D (D ψ) t‖ * M0 + 2 * 1 * ‖D ψ t‖ * M1 + 1 ^ 2 * ‖ψ t‖ * M2 := by
              exact add_le_add
                (add_le_add (mul_le_mul_of_nonneg_left (hM0 _) (norm_nonneg _))
                  (mul_le_mul
                    (mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left (ha N) (by norm_num)) (norm_nonneg _))
                    (hM1 _) (norm_nonneg _) (by positivity)))
                (mul_le_mul
                  (mul_le_mul_of_nonneg_right
                    (pow_le_pow_left₀ (norm_nonneg _) (ha N) 2) (norm_nonneg _))
                  (hM2 _) (norm_nonneg _) (by positivity))
            _ = _ := by ring
    change ‖(D (D (ψ - φ N))) t‖ ≤ _
    simp only [map_sub, SchwartzMap.sub_apply]
    calc
      _ ≤ ‖D (D ψ) t‖ + ‖D (D (φ N)) t‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have h0 : Tendsto (fun N => ∫ t : ℝ, ‖F N t‖) atTop (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (f := fun _ : ℝ => (0 : ℝ)) (fun t => (1 + M0) * ‖ψ t‖)
      (fun N => (F N).continuous.norm.aestronglyMeasurable)
      (ψ.integrable.norm.const_mul (1 + M0))
      (fun N => Eventually.of_forall (fun t => by simpa only [norm_norm] using hb0 N t))
      (Eventually.of_forall (fun t => by simpa only [norm_zero] using (hlim0 t).norm))
  have h2 : Tendsto (fun N => ∫ t : ℝ, ‖D (D (F N)) t‖) atTop (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (f := fun _ : ℝ => (0 : ℝ))
      (fun t => (1 + M0) * ‖D (D ψ) t‖ + 2 * M1 * ‖D ψ t‖ + M2 * ‖ψ t‖)
      (fun N => (D (D (F N))).continuous.norm.aestronglyMeasurable)
      ((((D (D ψ)).integrable.norm.const_mul (1 + M0)).add
        ((D ψ).integrable.norm.const_mul (2 * M1))).add (ψ.integrable.norm.const_mul M2))
      (fun N => Eventually.of_forall (fun t => by simpa only [norm_norm] using hb2 N t))
      (Eventually.of_forall (fun t => by simpa only [norm_zero] using (hlim2 t).norm))
  simpa only [tauberianFourierSize, D, F, φ, mul_zero, add_zero] using
    h0.add (h2.const_mul (4 * Real.pi ^ 2)⁻¹)

theorem exists_hasCompactSupport_tauberianFourierSize_sub_lt (ψ : 𝓢(ℝ, ℂ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : 𝓢(ℝ, ℂ), HasCompactSupport (φ : ℝ → ℂ) ∧ tauberianFourierSize (ψ - φ) < ε := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hb : ContDiff ℝ ∞ (fun t : ℝ => (b t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hbs : HasCompactSupport (fun t : ℝ => (b t : ℂ)) :=
    b.hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  let χ : 𝓢(ℝ, ℂ) := schwartzMapOfHasCompactSupport (fun t : ℝ => (b t : ℂ)) hb hbs
  have hχ : HasCompactSupport (χ : ℝ → ℂ) := hbs
  have hχ0 : χ 0 = 1 := by
    change (b 0 : ℂ) = 1
    rw [b.one_of_mem_closedBall (by simp [b])]
    rfl
  have ht := tendsto_tauberianFourierSize_sub_schwartzCutoff ψ χ hχ hχ0
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨schwartzCutoff ψ χ hχ ((N : ℝ) + 1) (by positivity),
    hasCompactSupport_schwartzCutoff ψ χ hχ ((N : ℝ) + 1) (by positivity), hN⟩

end DirichletL

import Mathlib

/-!
Fourier identities for the Wiener-Ikehara route to CDT v2's lcm input
(supplied TeX 3291-3310). Based on the PrimeNumberTheoremAnd contributors,
Wiener.lean at revision 0766218b21b11ddf24103352ece7f0cb730945e0,
lines 130-310 and 474-488. Original source and Apache 2.0 license
summation, bilinear Fourier interchange, and complex improper integrals
replace the corresponding support arguments.
-/

namespace DirichletL

open MeasureTheory Filter Set
open scoped Topology FourierTransform RealInnerProductSpace

theorem continuous_LSeries_vertical {f : ℕ → ℂ} {σ : ℝ}
    (hf : LSeriesSummable f (σ : ℂ)) :
    Continuous (fun t : ℝ => LSeries f ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hs : Summable (LSeries.term f (σ : ℂ)) := hf
  refine continuous_tsum (u := fun n => ‖LSeries.term f (σ : ℂ) n‖) ?_ hs.norm ?_
  · intro n
    by_cases hn : n = 0
    · simpa [hn] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
    have he : Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
    simpa only [LSeries.term_of_ne_zero hn] using
      (continuous_const (y := f n)).div
        (he.const_cpow (Or.inl (show (n : ℂ) ≠ 0 by exact_mod_cast hn)))
        (fun t => by simp [hn])
  · intro n t
    simp [LSeries.norm_term_eq]

theorem tauberianFourier_phase_term (f : ℕ → ℂ) (σ t : ℝ) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    LSeries.term f (σ : ℂ) n * Complex.exp (-(2 * (Real.pi : ℂ) * (t : ℂ) *
      ((1 / (2 * Real.pi) * Real.log ((n : ℝ) / x) : ℝ) : ℂ) * Complex.I)) =
      LSeries.term f ((σ : ℂ) + (t : ℂ) * Complex.I) n *
        (x : ℂ) ^ ((t : ℂ) * Complex.I) := by
  by_cases hn : n = 0
  · simp [hn]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hphase : -(2 * (Real.pi : ℂ) * (t : ℂ) *
      ((1 / (2 * Real.pi) * Real.log ((n : ℝ) / x) : ℝ) : ℂ) * Complex.I) =
      -(t : ℂ) * (Real.log ((n : ℝ) / x) : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [hphase, Real.log_div hnR hx.ne']
  simp only [LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero hnC,
    Complex.cpow_def_of_ne_zero hxC, Complex.ofReal_sub, Complex.natCast_log,
    Complex.ofReal_log hx.le, div_eq_mul_inv, ← Complex.exp_neg, mul_assoc,
    ← Complex.exp_add]
  congr 1
  congr 1
  ring

theorem tsum_tauberianFourier_eq_integral_LSeries {f : ℕ → ℂ} {σ : ℝ}
    (hf : LSeriesSummable f (σ : ℂ)) {ψ : ℝ → ℂ} (hψ : Integrable ψ)
    {x : ℝ} (hx : 0 < x) :
    (∑' n, LSeries.term f (σ : ℂ) n *
      𝓕 ψ (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x))) =
      ∫ t : ℝ, LSeries f ((σ : ℂ) + (t : ℂ) * Complex.I) * ψ t *
        (x : ℂ) ^ ((t : ℂ) * Complex.I) := by
  let ω (n : ℕ) := 1 / (2 * Real.pi) * Real.log ((n : ℝ) / x)
  let K (n : ℕ) (t : ℝ) :=
    Complex.exp (-(2 * (Real.pi : ℂ) * (t : ℂ) * (ω n : ℂ) * Complex.I))
  have hK (n : ℕ) (t : ℝ) : ‖K n t‖ = 1 := by simp [K, Complex.norm_exp]
  have hKc (n : ℕ) : Continuous (K n) := by dsimp [K]; fun_prop
  have hi (n : ℕ) : Integrable (fun t => LSeries.term f (σ : ℂ) n * K n t * ψ t) := by
    simpa only [mul_assoc] using (hψ.bdd_mul (hKc n).aestronglyMeasurable
      ⟨1, fun t => (hK n t).le⟩).const_mul (LSeries.term f (σ : ℂ) n)
  have hs : Summable (LSeries.term f (σ : ℂ)) := hf
  have hsum : Summable (fun n => ∫ t : ℝ, ‖LSeries.term f (σ : ℂ) n * K n t * ψ t‖) := by
    simpa only [norm_mul, hK, mul_one, integral_const_mul] using
      hs.norm.mul_right (∫ t : ℝ, ‖ψ t‖)
  calc
    _ = ∑' n, ∫ t : ℝ, LSeries.term f (σ : ℂ) n * K n t * ψ t := by
      apply tsum_congr
      intro n
      rw [Real.fourierIntegral_eq']
      simp only [RCLike.inner_apply', conj_trivial, smul_eq_mul]
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro t
      dsimp [K, ω]
      push_cast
      ring_nf
    _ = ∫ t : ℝ, ∑' n, LSeries.term f (σ : ℂ) n * K n t * ψ t :=
      integral_tsum_of_summable_integral_norm hi hsum
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro t
      have hv : Summable (LSeries.term f ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
        hf.of_re_le_re (by simp)
      calc
        _ = ∑' n, LSeries.term f ((σ : ℂ) + (t : ℂ) * Complex.I) n *
            (ψ t * (x : ℂ) ^ ((t : ℂ) * Complex.I)) := by
          apply tsum_congr
          intro n
          rw [show LSeries.term f (σ : ℂ) n * K n t =
            LSeries.term f ((σ : ℂ) + (t : ℂ) * Complex.I) n *
              (x : ℂ) ^ ((t : ℂ) * Complex.I) from tauberianFourier_phase_term f σ t hx n]
          ring
        _ = _ := by
          rw [hv.tsum_mul_right]
          exact (mul_assoc _ _ _).symm

theorem integral_tauberian_exponential {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) (t : ℝ) :
    (∫ u in Ici (-Real.log x), Complex.exp ((1 - (σ : ℂ) - (t : ℂ) * Complex.I) * (u : ℂ))) =
      ((x ^ (σ - 1) : ℝ) : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I - 1)⁻¹ *
        (x : ℂ) ^ ((t : ℂ) * Complex.I) := by
  rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_complex_Ioi (by simp; linarith)]
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  calc
    _ = Complex.exp ((Real.log x : ℂ) * (((σ : ℂ) - 1) + (t : ℂ) * Complex.I)) *
        ((σ : ℂ) + (t : ℂ) * Complex.I - 1)⁻¹ := by
      rw [neg_div, ← div_neg]
      push_cast
      ring_nf
    _ = (x : ℂ) ^ (((σ : ℂ) - 1) + (t : ℂ) * Complex.I) *
        ((σ : ℂ) + (t : ℂ) * Complex.I - 1)⁻¹ := by
      rw [Complex.cpow_def_of_ne_zero hxC, Complex.ofReal_log hx.le]
    _ = _ := by
      rw [Complex.cpow_add _ _ hxC]
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow hx.le]
      ring

theorem integral_tauberian_pole {ψ : ℝ → ℂ} (hψ : Integrable ψ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 < σ) :
    (∫ u in Ici (-Real.log x), (Real.exp (-u * (σ - 1)) : ℂ) *
      𝓕 ψ (u / (2 * Real.pi))) =
      ((x ^ (σ - 1) : ℝ) : ℂ) * ∫ t : ℝ,
        ((σ : ℂ) + (t : ℂ) * Complex.I - 1)⁻¹ * ψ t *
          (x : ℂ) ^ ((t : ℂ) * Complex.I) := by
  let L : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ := (1 / (2 * Real.pi)) • innerₗ ℝ
  let ν : Measure ℝ := volume.restrict (Ici (-Real.log x))
  let g (u : ℝ) : ℂ := Real.exp (-u * (σ - 1))
  have hL (t u : ℝ) : L t u = t * (u / (2 * Real.pi)) := by
    simp [L, innerₗ_apply, RCLike.inner_apply', div_eq_mul_inv]
    ring
  have hg : Integrable g ν := by
    have hi := integrableOn_exp_mul_complex_Ioi
      (show (1 - (σ : ℂ)).re < 0 by simp; linarith) (-Real.log x)
    apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
    convert hi using 1
    ext u
    rw [show (1 - (σ : ℂ)) * (u : ℂ) = ((-u * (σ - 1) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
  have hleft (u : ℝ) : VectorFourier.fourierIntegral Real.fourierChar volume L ψ u =
      𝓕 ψ (u / (2 * Real.pi)) := by
    simp only [Real.fourierIntegral, VectorFourier.fourierIntegral, hL,
      innerₗ_apply, RCLike.inner_apply', conj_trivial]
  have hright (t : ℝ) : VectorFourier.fourierIntegral Real.fourierChar ν L.flip g t =
      ((x ^ (σ - 1) : ℝ) : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I - 1)⁻¹ *
        (x : ℂ) ^ ((t : ℂ) * Complex.I) := by
    calc
      _ = ∫ u in Ici (-Real.log x),
          Complex.exp ((1 - (σ : ℂ) - (t : ℂ) * Complex.I) * (u : ℂ)) := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro u
        simp only [VectorFourier.fourierIntegral, LinearMap.flip_apply, hL,
          Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, g,
          Complex.ofReal_exp, ← Complex.exp_add]
        congr 1
        push_cast
        have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        field_simp
        ring
      _ = _ := integral_tauberian_exponential hx hσ t
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := L) (μ := volume) (ν := ν)
    Real.continuous_fourierChar (by simp only [hL]; fun_prop) hψ hg
  calc
    _ = ∫ u, (VectorFourier.fourierIntegral Real.fourierChar volume L ψ u) • g u ∂ν := by
      simp only [hleft, smul_eq_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun u => mul_comm _ _)
    _ = ∫ t : ℝ, ψ t • VectorFourier.fourierIntegral Real.fourierChar ν L.flip g t := hswap
    _ = _ := by
      simp only [hright, smul_eq_mul]
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => by ring)

end DirichletL

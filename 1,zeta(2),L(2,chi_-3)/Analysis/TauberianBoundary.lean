import Analysis.TauberianTransform
import Analysis.TauberianLimits

/-!
Compact-support boundary identity on the Wiener-Ikehara route to CDT v2,
Section 2.2 (supplied TeX 3291-3310). Based on the PrimeNumberTheoremAnd
contributors, Wiener.lean at revision 0766218b21b11ddf24103352ece7f0cb730945e0,
lines 482-523, 1020-1032, and 1068-1076. Original source and Apache 2.0
-/

namespace DirichletL

open MeasureTheory Filter Set
open scoped Topology FourierTransform SchwartzMap

theorem tauberian_residual_eq_integral {f : ℕ → ℂ} {A : ℂ} {G : ℂ → ℂ}
    (hG : EqOn G (fun s => LSeries f s - A / (s - 1)) {s | 1 < s.re})
    {σ : ℝ} (hf : LSeriesSummable f (σ : ℂ)) (hσ : 1 < σ)
    (ψ : 𝓢(ℝ, ℂ)) (hψ : HasCompactSupport (ψ : ℝ → ℂ)) {x : ℝ} (hx : 0 < x) :
    (∑' n, LSeries.term f (σ : ℂ) n *
      𝓕 ψ (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x))) -
        A * ((x ^ (1 - σ) : ℝ) : ℂ) *
          (∫ u in Ici (-Real.log x), (Real.exp (-u * (σ - 1)) : ℂ) *
            𝓕 ψ (u / (2 * Real.pi))) =
      ∫ t : ℝ, G ((σ : ℂ) + (t : ℂ) * Complex.I) * ψ t *
        (x : ℂ) ^ ((t : ℂ) * Complex.I) := by
  have hpow : Continuous (fun t : ℝ => (x : ℂ) ^ ((t : ℂ) * Complex.I)) :=
    (show Continuous (fun t : ℝ => (t : ℂ) * Complex.I) by fun_prop).const_cpow
      (Or.inl (by exact_mod_cast hx.ne'))
  have hi₁ : Integrable (fun t : ℝ => LSeries f ((σ : ℂ) + (t : ℂ) * Complex.I) *
      ψ t * (x : ℂ) ^ ((t : ℂ) * Complex.I)) :=
    (((continuous_LSeries_vertical hf).mul ψ.continuous).mul hpow).integrable_of_hasCompactSupport
      hψ.mul_left.mul_right
  have hd (t : ℝ) : (σ : ℂ) + (t : ℂ) * Complex.I - 1 ≠ 0 := by
    intro ht
    have hr := congrArg Complex.re ht
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero, Complex.one_re, Complex.zero_re] at hr
    linarith
  have hi₂ : Integrable (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I - 1)⁻¹ *
      ψ t * (x : ℂ) ^ ((t : ℂ) * Complex.I)) := by
    apply Continuous.integrable_of_hasCompactSupport _ hψ.mul_left.mul_right
    exact (((show Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I - 1) by
      fun_prop).inv₀ hd).mul ψ.continuous).mul hpow
  have hcancel : ((x ^ (1 - σ) : ℝ) : ℂ) * ((x ^ (σ - 1) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add hx]
    simp
  rw [tsum_tauberianFourier_eq_integral_LSeries hf ψ.integrable hx,
    integral_tauberian_pole ψ.integrable hx hσ]
  have hc (z : ℂ) : A * ((x ^ (1 - σ) : ℝ) : ℂ) *
      (((x ^ (σ - 1) : ℝ) : ℂ) * z) = A * z := by
    calc
      _ = A * (((x ^ (1 - σ) : ℝ) : ℂ) * ((x ^ (σ - 1) : ℝ) : ℂ)) * z := by ring
      _ = _ := by rw [hcancel, mul_one]
  rw [hc, ← integral_const_mul, ← integral_sub hi₁ (hi₂.const_mul A)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  dsimp only
  rw [hG (by simpa using hσ)]
  simp only [div_eq_mul_inv, sub_mul]
  ring

theorem tauberian_boundary_identity {f : ℕ → ℂ} {C : ℝ} {A : ℂ} {G : ℂ → ℂ}
    (hsum : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ C * n)
    (hf : ∀ σ : ℝ, 1 < σ → LSeriesSummable f (σ : ℂ))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : EqOn G (fun s => LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (ψ : 𝓢(ℝ, ℂ)) (hψ : HasCompactSupport (ψ : ℝ → ℂ)) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n, tauberianFourierTerm f ψ x n) -
        A * (∫ u in Ici (-Real.log x), 𝓕 ψ (u / (2 * Real.pi))) =
      ∫ t : ℝ, G (1 + (t : ℂ) * Complex.I) * ψ t *
        (x : ℂ) ^ ((t : ℂ) * Complex.I) := by
  have hx' := zero_lt_one.trans_le hx
  apply tendsto_nhds_unique_of_eventuallyEq
    ((tendsto_tsum_tauberianFourierTerm_boundary hsum hx' ψ).sub
      (tendsto_tauberian_pole_integral A ψ hx))
    (tendsto_tauberian_boundary_integral hG ψ hψ hx')
  exact eventually_nhdsWithin_of_forall (fun σ hσ =>
    tauberian_residual_eq_integral hG' (hf σ hσ) hσ ψ hψ hx')

theorem tendsto_tauberian_residual_of_hasCompactSupport {f : ℕ → ℂ} {C : ℝ}
    {A : ℂ} {G : ℂ → ℂ} (hsum : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ C * n)
    (hf : ∀ σ : ℝ, 1 < σ → LSeriesSummable f (σ : ℂ))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : EqOn G (fun s => LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (ψ : 𝓢(ℝ, ℂ)) (hψ : HasCompactSupport (ψ : ℝ → ℂ)) :
    Tendsto (fun x : ℝ => (∑' n, tauberianFourierTerm f ψ x n) -
      A * (∫ u in Ici (-Real.log x), 𝓕 ψ (u / (2 * Real.pi)))) atTop (𝓝 0) := by
  apply (tendsto_integral_cpow_imaginary (fun t => G (1 + (t : ℂ) * Complex.I) * ψ t)).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact (tauberian_boundary_identity hsum hf hG hG' ψ hψ hx).symm

end DirichletL

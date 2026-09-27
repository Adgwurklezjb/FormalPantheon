import Analysis.DedekindEtaLogDerivative
import Analysis.ModularLogDerivativeDifferential

/-!
Affine eta cusp limits for the weight-four differential in Zagier (2009),
Section 5, equation (7). Holomorphy of the Euler factor at q=0 controls
the derivative of the logarithmic derivative. See
-/

namespace DirichletL

open Complex Filter Function.Periodic
open _root_.UpperHalfPlane hiding I
open scoped Real Topology

theorem differentiableOn_dedekindEta_affine (u v : ℝ) (hu : 0 < u) :
    DifferentiableOn ℂ (fun z : ℂ => dedekindEta ((u : ℂ) * z + (v : ℂ)))
      {z | 0 < z.im} := by
  intro z hz
  have hp : 0 < ((u : ℂ) * z + (v : ℂ)).im := by simpa using mul_pos hu hz
  have hA : DifferentiableAt ℂ (fun w : ℂ => (u : ℂ) * w + (v : ℂ)) z := by fun_prop
  exact ((differentiableOn_dedekindEta.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hp)).comp z
      hA).differentiableWithinAt

theorem dedekindEta_sq_affine_prod_ne_zero (m : Fin 4 → ℤ)
    (u v : Fin 4 → ℝ) (hu : ∀ j, 0 < u j) {z : ℂ} (hz : 0 < z.im) :
    (∏ j, (dedekindEta ((u j : ℂ) * z + (v j : ℂ)) ^ 2) ^ m j) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply zpow_ne_zero
  apply pow_ne_zero
  apply dedekindEta_ne_zero
  simpa using mul_pos (hu j) hz

theorem differentiableOn_dedekindEta_sq_affine_prod (m : Fin 4 → ℤ)
    (u v : Fin 4 → ℝ) (hu : ∀ j, 0 < u j) :
    DifferentiableOn ℂ (fun z : ℂ =>
      ∏ j, (dedekindEta ((u j : ℂ) * z + (v j : ℂ)) ^ 2) ^ m j) {z | 0 < z.im} := by
  apply DifferentiableOn.fun_finset_prod
  intro j _
  apply ((differentiableOn_dedekindEta_affine (u j) (v j) (hu j)).pow 2).zpow
  left
  intro z hz
  apply pow_ne_zero
  apply dedekindEta_ne_zero
  simpa using mul_pos (hu j) hz

theorem tendsto_deriv_modularLogDeriv_dedekindEta_affine (u v : ℝ) (hu : 0 < u) :
    Tendsto (fun τ : ℍ => deriv
      (modularLogDeriv (fun z : ℂ => dedekindEta ((u : ℂ) * z + (v : ℂ)))) τ)
      atImInfty (𝓝 0) := by
  let P (q : ℂ) : ℂ := q * logDeriv qEulerProduct q
  let q (z : ℂ) : ℂ := qParam 1 ((u : ℂ) * z + (v : ℂ))
  have hE : AnalyticAt ℂ qEulerProduct 0 :=
    differentiableOn_qEulerProduct.analyticAt (Metric.isOpen_ball.mem_nhds (by simp))
  have hP : AnalyticAt ℂ P 0 :=
    analyticAt_id.mul (hE.deriv.div hE (by simp))
  have hq : Tendsto (fun τ : ℍ => q τ) atImInfty (𝓝 0) := tendsto_qParam_affine u v hu
  have hPd := hP.deriv.continuousAt.tendsto.comp hq
  have ht := (hPd.mul ((hq.const_mul (2 * π * I)).mul_const (u : ℂ))).const_mul (u : ℂ)
  simp only [mul_zero, zero_mul] at ht
  apply ht.congr'
  filter_upwards [hq.eventually (hP.eventually_analyticAt.mono
    (fun z hz => hz.differentiableAt))] with τ hτ
  have hA : HasDerivAt (fun z : ℂ => (u : ℂ) * z + (v : ℂ)) (u : ℂ) (τ : ℂ) := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id (τ : ℂ)).const_mul (u : ℂ)).add_const (v : ℂ)
  have hdq := (hasDerivAt_qParam_one ((u : ℂ) * τ + (v : ℂ))).comp (τ : ℂ) hA
  have hF := ((hτ.hasDerivAt.comp (τ : ℂ) hdq).const_add (1 / 24 : ℂ)).const_mul (u : ℂ)
  have he : modularLogDeriv (fun z : ℂ => dedekindEta ((u : ℂ) * z + (v : ℂ)))
      =ᶠ[𝓝 (τ : ℂ)] (fun z : ℂ => (u : ℂ) * (1 / 24 + P (q z))) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos]
      with z hz
    exact modularLogDeriv_dedekindEta_affine u v hu hz
  exact (he.deriv_eq.trans hF.deriv).symm

theorem tendsto_deriv_modularLogDeriv_dedekindEta_sq_affine_prod (m : Fin 4 → ℤ)
    (u v : Fin 4 → ℝ) (hu : ∀ j, 0 < u j) :
    Tendsto (fun τ : ℍ => deriv (modularLogDeriv (fun z : ℂ =>
      ∏ j, (dedekindEta ((u j : ℂ) * z + (v j : ℂ)) ^ 2) ^ m j)) τ)
      atImInfty (𝓝 0) := by
  have ht := tendsto_finset_sum Finset.univ (fun j _ =>
    (tendsto_deriv_modularLogDeriv_dedekindEta_affine (u j) (v j) (hu j)).const_mul
      (2 * (m j : ℂ)))
  simp only [mul_zero, Finset.sum_const_zero] at ht
  apply ht.congr'
  apply Filter.Eventually.of_forall
  intro τ
  have hL (j : Fin 4) : DifferentiableAt ℂ
      (modularLogDeriv (fun z : ℂ => dedekindEta ((u j : ℂ) * z + (v j : ℂ)))) τ := by
    apply (differentiableOn_modularLogDeriv
      (differentiableOn_dedekindEta_affine (u j) (v j) (hu j))
      (fun z hz => dedekindEta_ne_zero (by simpa using mul_pos (hu j) hz))).differentiableAt
    exact (isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos
  have hsum := HasDerivAt.sum (u := Finset.univ)
    (fun j _ => (hL j).hasDerivAt.const_mul (2 * (m j : ℂ)))
  have he : modularLogDeriv (fun z : ℂ =>
      ∏ j, (dedekindEta ((u j : ℂ) * z + (v j : ℂ)) ^ 2) ^ m j)
      =ᶠ[𝓝 (τ : ℂ)] (fun z : ℂ => ∑ j, 2 * (m j : ℂ) *
        modularLogDeriv (fun w : ℂ => dedekindEta ((u j : ℂ) * w + (v j : ℂ))) z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos]
      with z hz
    exact modularLogDeriv_dedekindEta_sq_affine_prod m u v hu hz
  exact (he.deriv_eq.trans hsum.deriv).symm

theorem tendsto_modularLogDerivCorrection_dedekindEta_sq_affine_prod (m : Fin 4 → ℤ)
    (u v : Fin 4 → ℝ) (hu : ∀ j, 0 < u j) :
    Tendsto (fun τ : ℍ => modularLogDerivCorrection (fun z : ℂ =>
      ∏ j, (dedekindEta ((u j : ℂ) * z + (v j : ℂ)) ^ 2) ^ m j) τ)
      atImInfty (𝓝 (((∑ j, (m j : ℂ) * (u j : ℂ)) / 12) ^ 2)) := by
  have hL := tendsto_modularLogDeriv_dedekindEta_sq_affine_prod m u v hu
  have hdL := tendsto_deriv_modularLogDeriv_dedekindEta_sq_affine_prod m u v hu
  simpa only [modularLogDerivCorrection, mul_zero, zero_div, sub_zero] using
    (hL.pow 2).sub ((hdL.const_mul 2).div_const (2 * π * I))

end DirichletL

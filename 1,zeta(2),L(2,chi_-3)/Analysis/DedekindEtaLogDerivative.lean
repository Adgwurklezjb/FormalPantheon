import Analysis.DedekindEtaCuspBounds
import Analysis.ModularLogDerivative

/-!
Affine eta logarithmic derivatives for Zagier (2009), Section 5,
equation (7), and CDT v2 Section 11.1. The cusp limit follows from
the eta product (DLMF 27.14.12) and holomorphy of its Euler factor at zero.
-/

namespace DirichletL

open Complex Filter Function.Periodic
open _root_.UpperHalfPlane hiding I
open scoped Real Topology

theorem hasDerivAt_qParam_one (z : ℂ) :
    HasDerivAt (qParam 1) (2 * π * I * qParam 1 z) z := by
  unfold qParam
  simpa only [ofReal_one, div_one, id_eq, mul_one, one_mul, mul_comm] using
    ((hasDerivAt_id z).const_mul (2 * π * I)).cexp

theorem modularLogDeriv_dedekindEta {z : ℂ} (hz : 0 < z.im) :
    modularLogDeriv dedekindEta z =
      1 / 24 + qParam 1 z * logDeriv qEulerProduct (qParam 1 z) := by
  have hq := hasDerivAt_qParam_one z
  have hp : DifferentiableAt ℂ qEulerProduct (qParam 1 z) :=
    differentiableOn_qEulerProduct.differentiableAt
      (Metric.isOpen_ball.mem_nhds (by simpa using norm_qParam_one_lt_one hz))
  have he := (((hasDerivAt_id z).const_mul (π * I)).div_const 12).cexp
  simp only [id_eq, mul_one] at he
  have hel : logDeriv (fun w : ℂ => exp (π * I * w / 12)) z = π * I / 12 := by
    rw [logDeriv_apply, he.deriv]
    field_simp
  have hpl := logDeriv_comp (g := qParam 1) hp hq.differentiableAt
  simp only [Function.comp_def, hq.deriv] at hpl
  change logDeriv (fun w : ℂ => exp (π * I * w / 12) * qEulerProduct (qParam 1 w)) z /
    (2 * π * I) = _
  rw [logDeriv_mul (f := fun w : ℂ => exp (π * I * w / 12))
    (g := fun w : ℂ => qEulerProduct (qParam 1 w))
    z (exp_ne_zero _) (qEulerProduct_ne_zero (norm_qParam_one_lt_one hz))
    he.differentiableAt (hp.comp z hq.differentiableAt), hel, hpl]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero, I_ne_zero]
  ring

theorem modularLogDeriv_dedekindEta_affine (u v : ℝ) (hu : 0 < u) {z : ℂ}
    (hz : 0 < z.im) :
    modularLogDeriv (fun w : ℂ => dedekindEta ((u : ℂ) * w + (v : ℂ))) z =
      u * (1 / 24 + qParam 1 ((u : ℂ) * z + (v : ℂ)) *
        logDeriv qEulerProduct (qParam 1 ((u : ℂ) * z + (v : ℂ)))) := by
  have hp : 0 < ((u : ℂ) * z + (v : ℂ)).im := by
    simpa using mul_pos hu hz
  have hd := ((hasDerivAt_id z).const_mul (u : ℂ)).add_const (v : ℂ)
  simp only [id_eq, mul_one] at hd
  have h := logDeriv_comp (g := fun w : ℂ => (u : ℂ) * w + (v : ℂ))
    (differentiableOn_dedekindEta.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hp)) hd.differentiableAt
  simp only [Function.comp_def, hd.deriv, mul_one] at h
  calc
    _ = u * modularLogDeriv dedekindEta ((u : ℂ) * z + (v : ℂ)) := by
      simp only [modularLogDeriv, h]
      ring
    _ = _ := by rw [modularLogDeriv_dedekindEta hp]

theorem tendsto_modularLogDeriv_dedekindEta_affine (u v : ℝ) (hu : 0 < u) :
    Tendsto (fun τ : ℍ =>
      modularLogDeriv (fun z : ℂ => dedekindEta ((u : ℂ) * z + (v : ℂ))) τ)
      atImInfty (𝓝 ((u : ℂ) / 24)) := by
  have hp : AnalyticAt ℂ qEulerProduct 0 :=
    differentiableOn_qEulerProduct.analyticAt (Metric.isOpen_ball.mem_nhds (by simp))
  have hl : ContinuousAt (logDeriv qEulerProduct) 0 :=
    hp.deriv.continuousAt.div hp.continuousAt (by simp)
  have hq := tendsto_qParam_affine u v hu
  have ht := (tendsto_const_nhds (x := (1 / 24 : ℂ))).add (hq.mul (hl.tendsto.comp hq))
  simp only [Function.comp_def, zero_mul, add_zero] at ht
  convert ht.const_mul (u : ℂ) using 1
  · ext τ
    exact modularLogDeriv_dedekindEta_affine u v hu τ.im_pos
  · rw [mul_one_div]

theorem modularLogDeriv_dedekindEta_sq_affine_prod (m : Fin 4 → ℤ)
    (u v : Fin 4 → ℝ) (hu : ∀ j, 0 < u j) {z : ℂ} (hz : 0 < z.im) :
    modularLogDeriv (fun w : ℂ =>
      ∏ j, (dedekindEta ((u j : ℂ) * w + (v j : ℂ)) ^ 2) ^ m j) z =
      ∑ j, (2 * (m j : ℂ)) *
        modularLogDeriv (fun w : ℂ => dedekindEta ((u j : ℂ) * w + (v j : ℂ))) z := by
  have hp (j : Fin 4) : 0 < ((u j : ℂ) * z + (v j : ℂ)).im := by
    simpa using mul_pos (hu j) hz
  have hd (j : Fin 4) :
      DifferentiableAt ℂ (fun w : ℂ => dedekindEta ((u j : ℂ) * w + (v j : ℂ))) z :=
    (differentiableOn_dedekindEta.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds (hp j))).comp z
      (((differentiableAt_const (c := (u j : ℂ))).mul differentiableAt_id).add_const (v j : ℂ))
  have h0 (j : Fin 4) : dedekindEta ((u j : ℂ) * z + (v j : ℂ)) ^ 2 ≠ 0 :=
    pow_ne_zero _ (dedekindEta_ne_zero (hp j))
  unfold modularLogDeriv
  rw [logDeriv_prod Finset.univ
    (fun j (w : ℂ) => (dedekindEta ((u j : ℂ) * w + (v j : ℂ)) ^ 2) ^ m j) z
    (fun j _ => zpow_ne_zero _ (h0 j)) (fun j _ => ((hd j).pow 2).zpow (Or.inl (h0 j)))]
  simp_rw [logDeriv_fun_zpow ((hd _).fun_pow 2), logDeriv_fun_pow (hd _)]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  norm_num only [Nat.cast_ofNat]
  ring

theorem tendsto_modularLogDeriv_dedekindEta_sq_affine_prod (m : Fin 4 → ℤ)
    (u v : Fin 4 → ℝ) (hu : ∀ j, 0 < u j) :
    Tendsto (fun τ : ℍ => modularLogDeriv (fun z : ℂ =>
      ∏ j, (dedekindEta ((u j : ℂ) * z + (v j : ℂ)) ^ 2) ^ m j) τ)
      atImInfty (𝓝 ((∑ j, (m j : ℂ) * (u j : ℂ)) / 12)) := by
  have ht := tendsto_finset_sum Finset.univ (fun j _ =>
    (tendsto_modularLogDeriv_dedekindEta_affine (u j) (v j) (hu j)).const_mul (2 * (m j : ℂ)))
  have hc : (∑ j, 2 * (m j : ℂ) * ((u j : ℂ) / 24)) =
      (∑ j, (m j : ℂ) * (u j : ℂ)) / 12 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hc] at ht
  convert ht using 1
  ext τ
  exact modularLogDeriv_dedekindEta_sq_affine_prod m u v hu τ.im_pos

end DirichletL

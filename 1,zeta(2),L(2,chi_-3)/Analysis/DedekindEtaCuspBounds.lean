import Analysis.DedekindEta
import Analysis.ModularSlash

/-!
Analytic bounds for affine eta products at the cusps in Zagier (2009),
Section 5, case C, and CDT v2 Section 11.1. The exponential slope may
be zero; only a nonnegative total slope is required for boundedness.
-/

namespace DirichletL

open Complex Filter Function.Periodic
open _root_.UpperHalfPlane hiding I
open scoped Real Topology

theorem tendsto_qParam_affine (u v : ℝ) (hu : 0 < u) :
    Tendsto (fun τ : ℍ => qParam 1 ((u : ℂ) * τ + (v : ℂ))) atImInfty (𝓝 0) := by
  have hi : Tendsto (fun τ : ℍ => ((u : ℂ) * τ + (v : ℂ)).im) atImInfty atTop := by
    simpa using (tendsto_comap : Tendsto UpperHalfPlane.im atImInfty atTop).const_mul_atTop hu
  have hz : Tendsto (fun τ : ℍ => (u : ℂ) * τ + (v : ℂ))
      atImInfty (comap Complex.im atTop) := tendsto_comap_iff.mpr hi
  exact ((qParam_tendsto (h := 1) (by norm_num)).comp hz).mono_right nhdsWithin_le_nhds

theorem dedekindEta_sq_zpow_eq_exp (z : ℂ) (m : ℤ) :
    (dedekindEta z ^ 2) ^ m =
      exp ((m : ℂ) * π * I * z / 6) * (qEulerProduct (qParam 1 z) ^ 2) ^ m := by
  have he : (exp (π * I * z / 12) ^ 2) ^ m = exp ((m : ℂ) * π * I * z / 6) := by
    rw [← exp_nat_mul, ← exp_int_mul]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  simp only [dedekindEta, mul_pow, mul_zpow, he]

theorem dedekindEta_sq_prod_eq_exp (m : Fin 4 → ℤ) (z : Fin 4 → ℂ) :
    (∏ j, (dedekindEta (z j) ^ 2) ^ m j) =
      exp (π * I / 6 * ∑ j, (m j : ℂ) * z j) *
        ∏ j, (qEulerProduct (qParam 1 (z j)) ^ 2) ^ m j := by
  simp_rw [dedekindEta_sq_zpow_eq_exp]
  rw [Finset.prod_mul_distrib, ← exp_sum]
  have he : (∑ j, (m j : ℂ) * π * I * z j / 6) =
      π * I / 6 * ∑ j, (m j : ℂ) * z j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]

private theorem norm_eta_affine_exp_le_one (m : Fin 4 → ℤ) (u v : Fin 4 → ℝ)
    (hs : 0 ≤ ∑ j, (m j : ℝ) * u j) (τ : ℍ) :
    ‖exp (π * I / 6 * ∑ j, (m j : ℂ) * ((u j : ℂ) * τ + (v j : ℂ)))‖ ≤ 1 := by
  have him : (∑ j, (m j : ℂ) * ((u j : ℂ) * τ + (v j : ℂ))).im =
      (∑ j, (m j : ℝ) * u j) * τ.im := by
    simp [Fin.sum_univ_four, Complex.mul_im, add_mul, mul_assoc]
  have hre : (π * I / 6 * ∑ j, (m j : ℂ) * ((u j : ℂ) * τ + (v j : ℂ))).re =
      -(Real.pi / 6) * ((∑ j, (m j : ℝ) * u j) * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im, him]
  rw [norm_exp, Real.exp_le_one_iff, hre]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity))
    (mul_nonneg hs τ.im_pos.le)

theorem isBoundedAtImInfty_dedekindEta_sq_affine_prod (m : Fin 4 → ℤ)
    (u v : Fin 4 → ℝ) (hu : ∀ j, 0 < u j) (hs : 0 ≤ ∑ j, (m j : ℝ) * u j) :
    IsBoundedAtImInfty
      (fun τ : ℍ => ∏ j, (dedekindEta ((u j : ℂ) * τ + (v j : ℂ)) ^ 2) ^ m j) := by
  have hE : IsBoundedAtImInfty
      (fun τ : ℍ => exp (π * I / 6 * ∑ j, (m j : ℂ) * ((u j : ℂ) * τ + (v j : ℂ)))) :=
    isBoundedAtImInfty_iff.mpr ⟨1, 0, fun τ _ => norm_eta_affine_exp_le_one m u v hs τ⟩
  have hc : ContinuousAt qEulerProduct 0 :=
    differentiableOn_qEulerProduct.continuousOn.continuousAt
      (Metric.isOpen_ball.mem_nhds (by simp))
  have hP : IsBoundedAtImInfty
      (fun τ : ℍ => ∏ j, (qEulerProduct (qParam 1 ((u j : ℂ) * τ + (v j : ℂ))) ^ 2) ^ m j) := by
    apply isBoundedAtImInfty_finset_prod
    intro j _
    have ht : Tendsto (fun τ : ℍ => qEulerProduct (qParam 1 ((u j : ℂ) * τ + (v j : ℂ))))
        atImInfty (𝓝 1) := by
      simpa only [Function.comp_apply, qEulerProduct_zero] using
        hc.tendsto.comp (tendsto_qParam_affine (u j) (v j) (hu j))
    exact ((ht.pow 2).zpow₀ (m j) (Or.inl (by simp))).isBigO_one ℝ
  change BoundedAtFilter atImInfty _
  convert BoundedAtFilter.mul hE hP using 1
  ext τ
  exact dedekindEta_sq_prod_eq_exp m (fun j => (u j : ℂ) * τ + (v j : ℂ))

end DirichletL

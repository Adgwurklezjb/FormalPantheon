import Analysis.ZagierSecondDerivativeAnalytic
import Analysis.ZagierLogDifferential
import Analysis.ZagierModularIdentity

/-!
Zagier's second case-C modular differential identity, Section 5, equation
(7) of Zagier (2009). The weight-four difference vanishes by its exact
order-five bound at infinity. See
denominator checks.
-/

namespace DirichletL

open Complex Filter Function.Periodic
open _root_.UpperHalfPlane hiding I
open scoped Topology MatrixGroups ModularForm Real

/-- The q-coordinate expression of the second modular difference. -/
noncomputable def zagierSecondDerivativeDifferenceProduct (q : ℂ) : ℂ :=
  zagierSecondClearedAnalytic q / (zagierCaseCNAnalytic q ^ 2 * zagierCaseCDAnalytic q ^ 2)

theorem modularLogDeriv_zagierEtaSquare_eq_clearA (τ : ℍ)
    (hN : DifferentiableAt ℂ zagierCaseCNAnalytic (qParam 1 τ))
    (hD : DifferentiableAt ℂ zagierCaseCDAnalytic (qParam 1 τ))
    (hN0 : zagierCaseCNAnalytic (qParam 1 τ) ≠ 0)
    (hD0 : zagierCaseCDAnalytic (qParam 1 τ) ≠ 0) :
    modularLogDeriv zagierEtaSquare τ =
      zagierClearAAnalytic (qParam 1 τ) /
        (zagierCaseCNAnalytic (qParam 1 τ) * zagierCaseCDAnalytic (qParam 1 τ)) := by
  let q : ℂ := qParam 1 τ
  have he : zagierEtaSquare =ᶠ[𝓝 (τ : ℂ)]
      (fun z : ℂ => zagierEtaSquareProduct (qParam 1 z)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos]
      with z hz
    exact zagierEtaSquare_eq_product ⟨z, hz⟩
  have hg : DifferentiableAt ℂ zagierEtaSquareProduct q := hN.div hD hD0
  have hc := logDeriv_comp hg (hasDerivAt_qParam_one (τ : ℂ)).differentiableAt
  have hc' : logDeriv (fun z : ℂ => zagierEtaSquareProduct (qParam 1 z)) τ =
      logDeriv zagierEtaSquareProduct q * deriv (qParam 1) τ := hc
  have hd : deriv zagierEtaSquareProduct q =
      (deriv zagierCaseCNAnalytic q * zagierCaseCDAnalytic q -
        zagierCaseCNAnalytic q * deriv zagierCaseCDAnalytic q) /
          zagierCaseCDAnalytic q ^ 2 := (hN.hasDerivAt.div hD.hasDerivAt hD0).deriv
  have hπ : (2 * π * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero))
      I_ne_zero
  unfold modularLogDeriv
  rw [logDeriv_eq_of_eventuallyEq he, hc', logDeriv_apply, hd,
    (hasDerivAt_qParam_one (τ : ℂ)).deriv]
  change (((deriv zagierCaseCNAnalytic q * zagierCaseCDAnalytic q -
      zagierCaseCNAnalytic q * deriv zagierCaseCDAnalytic q) /
        zagierCaseCDAnalytic q ^ 2 /
          (zagierCaseCNAnalytic q / zagierCaseCDAnalytic q)) * (2 * π * I * q)) /
      (2 * π * I) =
    (q * deriv zagierCaseCNAnalytic q * zagierCaseCDAnalytic q -
      zagierCaseCNAnalytic q * (q * deriv zagierCaseCDAnalytic q)) /
      (zagierCaseCNAnalytic q * zagierCaseCDAnalytic q)
  have hcalc (n d dn dd q c : ℂ) (hn : n ≠ 0) (hd : d ≠ 0) (hc : c ≠ 0) :
      (((dn * d - n * dd) / d ^ 2 / (n / d)) * (c * q)) / c =
        (q * dn * d - n * (q * dd)) / (n * d) := by
    field_simp [hn, hd, hc]
  exact hcalc _ _ _ _ _ _ hN0 hD0 hπ

theorem zagierSecondDerivativeDifferenceForm_eq_product (τ : ℍ)
    (hN : AnalyticAt ℂ zagierCaseCNAnalytic (qParam 1 τ))
    (hD : AnalyticAt ℂ zagierCaseCDAnalytic (qParam 1 τ))
    (hA : AnalyticAt ℂ zagierClearAAnalytic (qParam 1 τ))
    (hN0 : zagierCaseCNAnalytic (qParam 1 τ) ≠ 0)
    (hD0 : zagierCaseCDAnalytic (qParam 1 τ) ≠ 0) :
    zagierSecondDerivativeDifferenceForm τ =
      zagierSecondDerivativeDifferenceProduct (qParam 1 τ) := by
  let q : ℂ := qParam 1 τ
  have hq := (hasDerivAt_qParam_one (τ : ℂ)).continuousAt.tendsto
  have he : modularLogDeriv zagierEtaSquare =ᶠ[𝓝 (τ : ℂ)]
      (fun z : ℂ => zagierClearAAnalytic (qParam 1 z) /
        (zagierCaseCNAnalytic (qParam 1 z) * zagierCaseCDAnalytic (qParam 1 z))) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos,
      hq.eventually hN.eventually_analyticAt, hq.eventually hD.eventually_analyticAt,
      hq.eventually (hN.differentiableAt.continuousAt.eventually_ne hN0),
      hq.eventually (hD.differentiableAt.continuousAt.eventually_ne hD0)]
      with z hz hn hd hn0 hd0
    exact modularLogDeriv_zagierEtaSquare_eq_clearA ⟨z, hz⟩
      hn.differentiableAt hd.differentiableAt hn0 hd0
  have hden : zagierCaseCNAnalytic q * zagierCaseCDAnalytic q ≠ 0 :=
    mul_ne_zero hN0 hD0
  have hL := hA.differentiableAt.hasDerivAt.fun_div
    (hN.differentiableAt.hasDerivAt.fun_mul hD.differentiableAt.hasDerivAt) hden
  have hLc := hL.comp (τ : ℂ) (hasDerivAt_qParam_one (τ : ℂ))
  have hLc' := hLc.deriv
  simp only [Function.comp_def] at hLc'
  have hπ : (2 * π * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero))
      I_ne_zero
  have hAeq : zagierClearAAnalytic q =
      q * deriv zagierCaseCNAnalytic q * zagierCaseCDAnalytic q -
        zagierCaseCNAnalytic q * (q * deriv zagierCaseCDAnalytic q) := rfl
  rw [zagierSecondDerivativeDifferenceForm_apply, modularLogDerivCorrection,
    he.eq_of_nhds, he.deriv_eq, hLc',
    hauptmodulEta_eq_product, zagierEtaSquare_eq_product]
  change (zagierClearAAnalytic q /
      (zagierCaseCNAnalytic q * zagierCaseCDAnalytic q)) ^ 2 -
    2 * (((deriv zagierClearAAnalytic q *
        (zagierCaseCNAnalytic q * zagierCaseCDAnalytic q) -
      zagierClearAAnalytic q * (deriv zagierCaseCNAnalytic q * zagierCaseCDAnalytic q +
        zagierCaseCNAnalytic q * deriv zagierCaseCDAnalytic q)) /
          (zagierCaseCNAnalytic q * zagierCaseCDAnalytic q) ^ 2) * (2 * π * I * q)) /
        (2 * π * I) -
      zagierClearPolynomialAnalytic q * (zagierCaseCNAnalytic q / zagierCaseCDAnalytic q) ^ 2 =
    (3 * zagierClearAAnalytic q ^ 2 -
      2 * zagierCaseCNAnalytic q *
        (q * deriv zagierClearAAnalytic q * zagierCaseCDAnalytic q -
          2 * zagierClearAAnalytic q * (q * deriv zagierCaseCDAnalytic q)) -
      zagierClearPolynomialAnalytic q * zagierCaseCNAnalytic q ^ 4) /
        (zagierCaseCNAnalytic q ^ 2 * zagierCaseCDAnalytic q ^ 2)
  have hcalc (n d a dn dd da q c p : ℂ)
      (hn : n ≠ 0) (hd : d ≠ 0) (hc : c ≠ 0)
      (ha : a = q * dn * d - n * (q * dd)) :
      (a / (n * d)) ^ 2 -
          2 * (((da * (n * d) - a * (dn * d + n * dd)) / (n * d) ^ 2) * (c * q)) / c -
          p * (n / d) ^ 2 =
        (3 * a ^ 2 - 2 * n * (q * da * d - 2 * a * (q * dd)) - p * n ^ 4) /
          (n ^ 2 * d ^ 2) := by
    have hnorm (x : ℂ) : 2 * (x * (c * q)) / c = 2 * x * q := by
      field_simp [hc]
    have hp : p * (n / d) ^ 2 = p * n ^ 4 / (n * d) ^ 2 := by
      field_simp [hn, hd]
    rw [hnorm, hp, div_pow, ← mul_div_assoc, div_mul_eq_mul_div,
      ← sub_div, ← sub_div, ← mul_pow]
    congr 1
    rw [ha]
    ring
  exact hcalc _ _ _ _ _ _ _ _ _ hN0 hD0 hπ hAeq

theorem tendsto_div_fifth_zagierSecondDerivativeDifferenceProduct :
    Tendsto (fun q : ℂ => zagierSecondDerivativeDifferenceProduct q / q ^ 5) (𝓝[≠] 0)
      (𝓝 ((complexSeries (PowerSeries.map (Int.castRingHom ℚ)
        zagierSecondClearedSeries)).coeff 5)) := by
  have hN0 : zagierCaseCNAnalytic 0 = 1 := by
    simp [zagierCaseCNAnalytic, qEulerProduct_zero]
  have hD0 : zagierCaseCDAnalytic 0 = 1 := by
    simp [zagierCaseCDAnalytic, qEulerProduct_zero]
  have hN : Tendsto zagierCaseCNAnalytic (𝓝[≠] 0) (𝓝 1) := by
    rw [← hN0]
    exact hasFPowerSeriesAt_zagierCaseCNAnalytic.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hD : Tendsto zagierCaseCDAnalytic (𝓝[≠] 0) (𝓝 1) := by
    rw [← hD0]
    exact hasFPowerSeriesAt_zagierCaseCDAnalytic.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have ht := tendsto_div_fifth_zagierSecondClearedAnalytic.div
    ((hN.pow 2).mul (hD.pow 2)) (by norm_num : (1 ^ 2 * 1 ^ 2 : ℂ) ≠ 0)
  convert ht using 1
  · ext q
    dsimp only [zagierSecondDerivativeDifferenceProduct, Pi.div_apply]
    ring
  · norm_num

theorem zagierSecondDerivativeDifferenceForm_eventually_eq_product :
    (fun τ : ℍ => zagierSecondDerivativeDifferenceForm τ) =ᶠ[atImInfty]
      (fun τ : ℍ => zagierSecondDerivativeDifferenceProduct (qParam 1 τ)) := by
  have hq : Tendsto (fun τ : ℍ => qParam 1 τ) atImInfty (𝓝 0) :=
    ((qParam_tendsto (h := 1) (by norm_num)).comp tendsto_coe_atImInfty).mono_right
      nhdsWithin_le_nhds
  have hN := hasFPowerSeriesAt_zagierCaseCNAnalytic
  have hD := hasFPowerSeriesAt_zagierCaseCDAnalytic
  have hA := hasFPowerSeriesAt_zagierClearAAnalytic
  have hN0 : zagierCaseCNAnalytic 0 ≠ 0 := by
    simp [zagierCaseCNAnalytic, qEulerProduct_zero]
  have hD0 : zagierCaseCDAnalytic 0 ≠ 0 := by
    simp [zagierCaseCDAnalytic, qEulerProduct_zero]
  filter_upwards [hq.eventually hN.analyticAt.eventually_analyticAt,
    hq.eventually hD.analyticAt.eventually_analyticAt,
    hq.eventually hA.analyticAt.eventually_analyticAt,
    hq.eventually (hN.continuousAt.eventually_ne hN0),
    hq.eventually (hD.continuousAt.eventually_ne hD0)] with τ hn hd ha hn0 hd0
  exact zagierSecondDerivativeDifferenceForm_eq_product τ hn hd ha hn0 hd0

theorem zagierSecondDerivativeDifferenceForm_eq_zero :
    zagierSecondDerivativeDifferenceForm = 0 := by
  apply levelSix_eq_zero_of_bounded_div_qParam_pow (k := 4) (n := 5) (by norm_num)
  have hq0 : Tendsto (fun τ : ℍ => qParam 1 τ) atImInfty (𝓝 0) :=
    ((qParam_tendsto (h := 1) (by norm_num)).comp tendsto_coe_atImInfty).mono_right
      nhdsWithin_le_nhds
  have hq : Tendsto (fun τ : ℍ => qParam 1 τ) atImInfty (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hq0, Filter.Eventually.of_forall (fun τ => ?_)⟩
    exact exp_ne_zero _
  have ht := tendsto_div_fifth_zagierSecondDerivativeDifferenceProduct.comp hq
  have hb := ht.isBigO_one ℝ
  have he : (fun τ : ℍ => zagierSecondDerivativeDifferenceForm τ / qParam 1 τ ^ 5) =ᶠ[atImInfty]
      (fun τ : ℍ => zagierSecondDerivativeDifferenceProduct (qParam 1 τ) / qParam 1 τ ^ 5) := by
    filter_upwards [zagierSecondDerivativeDifferenceForm_eventually_eq_product] with τ hτ
    rw [hτ]
  change BoundedAtFilter atImInfty _
  exact hb.congr' he.symm (Filter.Eventually.of_forall (fun _ => rfl))

theorem zagier_second_modular_identity (τ : ℍ) :
    modularLogDerivCorrection zagierEtaSquare τ =
      4 * hauptmodulEta τ * (1 - 10 * hauptmodulEta τ + 9 * hauptmodulEta τ ^ 2) *
        (9 * hauptmodulEta τ - 3) * zagierEtaSquare τ ^ 2 := by
  have h := congrArg
    (fun f : ModularForm (CongruenceSubgroup.Gamma0 6) 4 => f τ)
    zagierSecondDerivativeDifferenceForm_eq_zero
  simpa only [zagierSecondDerivativeDifferenceForm_apply,
    ModularForm.zero_apply, sub_eq_zero] using h

end DirichletL

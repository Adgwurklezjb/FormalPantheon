import Analysis.ZagierClearedNumeratorAnalytic
import Analysis.HauptmodulLogDerivative
import Analysis.ZagierEtaModular
import Analysis.LevelSixVanishing

/-!
The case-C weight-two modular identity from CDT v2 Section 11.1. The
analytic numerator and modular forms are already constructed upstream; this
file transfers their order-three q-bound to the level-six vanishing theorem.
-/

namespace DirichletL

open Complex Filter Function.Periodic
open _root_.UpperHalfPlane hiding I
open scoped Topology Manifold MatrixGroups ModularForm CongruenceSubgroup Real

/-- The q-product for the square of Zagier's case-C eta quotient. -/
noncomputable def zagierEtaSquareProduct (q : ℂ) : ℂ :=
  (qEulerProduct (q ^ 2) ^ 12 * qEulerProduct (q ^ 3) ^ 2) /
    (qEulerProduct q ^ 6 * qEulerProduct (q ^ 6) ^ 4)

/-- The weight-two difference whose vanishing is Zagier's equation (7). -/
noncomputable def zagierDerivativeDifferenceForm :
    ModularForm (CongruenceSubgroup.Gamma0 6) 2 :=
  hauptmodulLogDerivativeForm - zagierEtaWeightTwoForm 0 +
    10 • zagierEtaWeightTwoForm 1 - 9 • zagierEtaWeightTwoForm 2

/-- The cleared q-coordinate difference, with the nonzero unit factors retained. -/
noncomputable def zagierDerivativeDifferenceProduct (q : ℂ) : ℂ :=
  hauptmodulDerivativeClearedNumeratorAnalytic q /
    (dslope hauptmodulProduct 0 q *
      (qEulerProduct q ^ 6 * qEulerProduct (q ^ 6) ^ 4))

theorem zagierEtaSquare_eq_product (τ : ℍ) :
    zagierEtaSquare τ = zagierEtaSquareProduct (qParam 1 τ) := by
  have hq1 : qEulerProduct (qParam 1 τ) ≠ 0 :=
    qEulerProduct_ne_zero (norm_qParam_one_lt_one τ.im_pos)
  have hq6 : qEulerProduct (qParam 1 τ ^ 6) ≠ 0 := by
    apply qEulerProduct_ne_zero
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (norm_qParam_one_lt_one τ.im_pos) (by norm_num)
  rw [zagierEtaSquare_eq, zagierEtaSquareProduct]
  have hq2 := qParam_one_nat_mul 2 (τ : ℂ)
  have hq3 := qParam_one_nat_mul 3 (τ : ℂ)
  have hq6' := qParam_one_nat_mul 6 (τ : ℂ)
  norm_num only [Nat.cast_ofNat] at hq2 hq3 hq6'
  simp only [dedekindEta, hq2, hq3, hq6']
  let a : ℂ := π * I * τ / 12
  have hB2 : exp (π * I * (2 * τ) / 12) = exp a ^ 2 := by
    rw [show (π * I * (2 * τ) / 12) = 2 * a by dsimp [a]; ring]
    simpa only [Nat.cast_ofNat] using (Complex.exp_nat_mul a 2)
  have hB1 : exp (π * I * τ / 12) = exp a := by rfl
  have hB3 : exp (π * I * (3 * τ) / 12) = exp a ^ 3 := by
    rw [show (π * I * (3 * τ) / 12) = 3 * a by dsimp [a]; ring]
    simpa only [Nat.cast_ofNat] using (Complex.exp_nat_mul a 3)
  have hB6 : exp (π * I * (6 * τ) / 12) = exp a ^ 6 := by
    rw [show (π * I * (6 * τ) / 12) = 6 * a by dsimp [a]; ring]
    simpa only [Nat.cast_ofNat] using (Complex.exp_nat_mul a 6)
  simp only [hB2, hB3, hB1, hB6]
  field_simp [hq1, hq6, Complex.exp_ne_zero] <;> ring

@[simp] theorem zagierDerivativeDifferenceForm_apply (τ : ℍ) :
    zagierDerivativeDifferenceForm τ =
      modularLogDeriv hauptmodulEta τ -
        (1 - 10 * hauptmodulEta τ + 9 * hauptmodulEta τ ^ 2) * zagierEtaSquare τ := by
  rw [zagierDerivativeDifferenceForm]
  simp only [ModularForm.sub_apply, ModularForm.add_apply, ModularForm.smul_apply,
    smul_eq_mul]
  norm_num only [nsmul_eq_mul]
  rw [hauptmodulLogDerivativeForm_apply, zagierEtaWeightTwoForm_eq,
    zagierEtaWeightTwoForm_eq, zagierEtaWeightTwoForm_eq]
  norm_num [zagierEtaSquare, pow_two]
  ring

theorem hauptmodulProduct_differentiableAt {q : ℂ} (hq : ‖q‖ < 1 / 2 ^ 25) :
    DifferentiableAt ℂ hauptmodulProduct q := by
  have hq1 : ‖q‖ < 1 := hq.trans (by norm_num)
  have hd : DifferentiableAt ℂ qEulerProduct q :=
    differentiableOn_qEulerProduct.differentiableAt
      (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using hq1))
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq1 (by norm_num)
  have hq3 : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq1 (by norm_num)
  have hq6 : ‖q ^ 6‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq1 (by norm_num)
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => qEulerProduct (z ^ 2)) q :=
    (differentiableOn_qEulerProduct.differentiableAt
      (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using hq2))).comp q
      (by fun_prop)
  have hd3 : DifferentiableAt ℂ (fun z : ℂ => qEulerProduct (z ^ 3)) q :=
    (differentiableOn_qEulerProduct.differentiableAt
      (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using hq3))).comp q
      (by fun_prop)
  have hd6 : DifferentiableAt ℂ (fun z : ℂ => qEulerProduct (z ^ 6)) q :=
    (differentiableOn_qEulerProduct.differentiableAt
      (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using hq6))).comp q
      (by fun_prop)
  have hn : DifferentiableAt ℂ
      (fun z : ℂ => z * qEulerProduct z ^ 4 * qEulerProduct (z ^ 6) ^ 8) q := by
    fun_prop
  have hdend : DifferentiableAt ℂ
      (fun z : ℂ => qEulerProduct (z ^ 2) ^ 8 * qEulerProduct (z ^ 3) ^ 4) q := by
    fun_prop
  have hne2 : qEulerProduct (q ^ 2) ^ 8 ≠ 0 :=
    pow_ne_zero _ (qEulerProduct_ne_zero hq2)
  have hne3 : qEulerProduct (q ^ 3) ^ 4 ≠ 0 :=
    pow_ne_zero _ (qEulerProduct_ne_zero hq3)
  unfold hauptmodulProduct
  exact hn.div hdend (mul_ne_zero hne2 hne3)

theorem modularLogDeriv_hauptmodulEta_eq_product {τ : ℍ}
    (hq : ‖qParam 1 τ‖ < 1 / 2 ^ 25) :
    modularLogDeriv hauptmodulEta τ =
      (dslope hauptmodulProduct 0 (qParam 1 τ) +
        qParam 1 τ * deriv (dslope hauptmodulProduct 0) (qParam 1 τ)) /
      dslope hauptmodulProduct 0 (qParam 1 τ) := by
  let q : ℂ := qParam 1 τ
  have hq0 : q ≠ 0 := exp_ne_zero _
  have hdH : DifferentiableAt ℂ hauptmodulProduct q :=
    hauptmodulProduct_differentiableAt (q := q) hq
  have hdr : DifferentiableAt ℂ (dslope hauptmodulProduct 0) q :=
    (differentiableAt_dslope_of_ne hq0).mpr hdH
  have hH0 : hauptmodulProduct 0 = 0 := by simp [hauptmodulProduct]
  have hHr : q * dslope hauptmodulProduct 0 q = hauptmodulProduct q := by
    have h := sub_smul_dslope hauptmodulProduct 0 q
    simpa only [sub_zero, hH0, smul_eq_mul, zero_sub, sub_zero, zero_add] using h
  have hEq : (fun z : ℂ => hauptmodulProduct z) =ᶠ[𝓝 q]
      (fun z : ℂ => z * dslope hauptmodulProduct 0 z) := by
    filter_upwards [isOpen_ne.mem_nhds hq0] with z hz
    have h := sub_smul_dslope hauptmodulProduct 0 z
    simpa only [sub_zero, hH0, smul_eq_mul, zero_sub, sub_zero, zero_add] using h.symm
  have hder : deriv hauptmodulProduct q =
      deriv (fun z : ℂ => z * dslope hauptmodulProduct 0 z) q := hEq.deriv_eq
  have hdermul : deriv (fun z : ℂ => z * dslope hauptmodulProduct 0 z) q =
      dslope hauptmodulProduct 0 q + q * deriv (dslope hauptmodulProduct 0) q := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id q).mul hdr.hasDerivAt).deriv
  have hlogH : logDeriv hauptmodulProduct q =
      (dslope hauptmodulProduct 0 q + q * deriv (dslope hauptmodulProduct 0) q) /
        (q * dslope hauptmodulProduct 0 q) := by
    rw [logDeriv_apply, hder, hdermul, hHr]
  have hEta : hauptmodulEta (τ : ℂ) = hauptmodulProduct q := hauptmodulEta_eq_product _
  have hHne : hauptmodulProduct q ≠ 0 := by
    rw [← hEta]
    exact hauptmodulEta_ne_zero τ.im_pos
  have hrne : dslope hauptmodulProduct 0 q ≠ 0 := by
    intro hr
    apply hHne
    rw [← hHr, hr, mul_zero]
  have hcomp := logDeriv_comp hdH (hasDerivAt_qParam_one (τ : ℂ)).differentiableAt
  have heq : logDeriv hauptmodulEta (τ : ℂ) =
      logDeriv (fun z : ℂ => hauptmodulProduct (qParam 1 z)) (τ : ℂ) := by
    apply logDeriv_eq_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun z => hauptmodulEta_eq_product z)
  unfold modularLogDeriv
  rw [heq]
  have hcomp' : logDeriv (fun z : ℂ => hauptmodulProduct (qParam 1 z)) (τ : ℂ) =
      logDeriv hauptmodulProduct (qParam 1 (τ : ℂ)) * deriv (qParam 1) (τ : ℂ) := by
    simpa only [Function.comp_def] using hcomp
  rw [hcomp', (hasDerivAt_qParam_one (τ : ℂ)).deriv, hlogH]
  dsimp [q]
  have hq0' : qParam 1 (τ : ℂ) ≠ 0 := exp_ne_zero _
  have hrne' : dslope hauptmodulProduct 0 (qParam 1 (τ : ℂ)) ≠ 0 := hrne
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hq0', hrne', hπ, I_ne_zero]

theorem tendsto_div_cube_zagierDerivativeDifferenceProduct :
    Tendsto (fun q : ℂ => zagierDerivativeDifferenceProduct q / q ^ 3)
      (𝓝[≠] 0)
      (𝓝 ((complexSeries hauptmodulDerivativeClearedNumeratorRat).coeff 3 / 1)) := by
  have hN := tendsto_div_cube_hauptmodulDerivativeClearedNumeratorAnalytic
  have hR0 : (complexSeries hauptmodulShiftRat).coeff 0 = 1 := by
    simp [complexSeries, hauptmodulShiftRat, formalShift, PowerSeries.coeff_map,
      Int.coe_castRingHom, Rat.cast_intCast, hauptmodulShift,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_hauptmodul,
      coeff_one_hauptmodul]
  have hRval : dslope hauptmodulProduct 0 0 =
      (complexSeries hauptmodulShiftRat).coeff 0 := by
    have h := hasFPowerSeriesAt_hauptmodulShift.coeff_zero (fun _ => 1)
    simpa only [one_smul] using h.symm
  have hR : Tendsto (dslope hauptmodulProduct 0) (𝓝[≠] 0) (𝓝 1) := by
    have ht := hasFPowerSeriesAt_hauptmodulShift.continuousAt.tendsto
    have ht' : Tendsto (dslope hauptmodulProduct 0) (𝓝 0) (𝓝 1) := by
      rw [← hR0, ← hRval]
      exact ht
    exact ht'.mono_left nhdsWithin_le_nhds
  have hQ : Tendsto qEulerProduct (𝓝 0) (𝓝 1) := by
    have hc : ContinuousAt qEulerProduct 0 :=
      differentiableOn_qEulerProduct.continuousOn.continuousAt
        (Metric.isOpen_ball.mem_nhds (by simp))
    simpa only [qEulerProduct_zero] using hc.tendsto
  have hQ6 : Tendsto (fun q : ℂ => qEulerProduct (q ^ 6)) (𝓝 0) (𝓝 1) := by
    have hp : Tendsto (fun q : ℂ => q ^ 6) (𝓝 0) (𝓝 0) :=
      by simpa using (continuousAt_id (x := (0 : ℂ))).pow 6 |>.tendsto
    simpa only [Function.comp_def] using hQ.comp hp
  have hD : Tendsto
      (fun q : ℂ => qEulerProduct q ^ 6 * qEulerProduct (q ^ 6) ^ 4)
      (𝓝[≠] 0) (𝓝 1) := by
    have ht := (hQ.pow 6).mul (hQ6.pow 4)
    simpa only [qEulerProduct_zero, one_pow, one_mul] using ht.mono_left nhdsWithin_le_nhds
  have hden := hR.mul hD
  have ht := hN.div hden (by norm_num : (1 * 1 : ℂ) ≠ 0)
  have ht' : Tendsto (fun q : ℂ => zagierDerivativeDifferenceProduct q / q ^ 3)
      (𝓝[≠] 0)
      (𝓝 ((complexSeries hauptmodulDerivativeClearedNumeratorRat).coeff 3 / (1 * 1))) := by
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with q hq0
    simp only [zagierDerivativeDifferenceProduct, Pi.div_apply]
    field_simp [hq0]
  simpa using ht'

theorem zagierDerivativeDifferenceForm_eq_product {τ : ℍ}
    (hq : ‖qParam 1 τ‖ < 1 / 2 ^ 25) :
    zagierDerivativeDifferenceForm τ =
      zagierDerivativeDifferenceProduct (qParam 1 τ) := by
  rw [zagierDerivativeDifferenceForm_apply,
    modularLogDeriv_hauptmodulEta_eq_product hq, hauptmodulEta_eq_product,
    zagierEtaSquare_eq_product τ]
  let q : ℂ := qParam 1 τ
  have hq1 : ‖q‖ < 1 := hq.trans (by norm_num)
  have hq6 : ‖q ^ 6‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq1 (by norm_num)
  have hHne : hauptmodulProduct q ≠ 0 := by
    rw [← hauptmodulEta_eq_product (τ : ℂ)]
    exact hauptmodulEta_ne_zero τ.im_pos
  have hrne : dslope hauptmodulProduct 0 q ≠ 0 := by
    intro hr
    apply hHne
    have h := sub_smul_dslope hauptmodulProduct 0 q
    have hH0 : hauptmodulProduct 0 = 0 := by simp [hauptmodulProduct]
    have h' : q * dslope hauptmodulProduct 0 q = hauptmodulProduct q := by
      simpa only [sub_zero, hH0, smul_eq_mul, zero_sub, sub_zero, zero_add] using h
    rw [← h', hr, mul_zero]
  have hTne : qEulerProduct q ^ 6 * qEulerProduct (q ^ 6) ^ 4 ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 6 (qEulerProduct_ne_zero hq1))
      (pow_ne_zero 4 (qEulerProduct_ne_zero hq6))
  unfold zagierDerivativeDifferenceProduct hauptmodulDerivativeClearedNumeratorAnalytic
  unfold zagierEtaSquareProduct
  have hcalc (r q d K S T : ℂ) (hr : r ≠ 0) (hT : T ≠ 0) :
      (r + q * d) / r - K * (S / T) =
        ((r + q * d) * T - K * S * r) / (r * T) := by
    field_simp [hr, hT]
  exact hcalc
    (dslope hauptmodulProduct 0 (qParam 1 τ))
    (qParam 1 τ)
    (deriv (dslope hauptmodulProduct 0) (qParam 1 τ))
    (1 - 10 * hauptmodulProduct (qParam 1 τ) + 9 * hauptmodulProduct (qParam 1 τ) ^ 2)
    (qEulerProduct (qParam 1 τ ^ 2) ^ 12 * qEulerProduct (qParam 1 τ ^ 3) ^ 2)
    (qEulerProduct (qParam 1 τ) ^ 6 * qEulerProduct (qParam 1 τ ^ 6) ^ 4)
    hrne hTne

theorem zagierDerivativeDifferenceForm_eq_zero :
    zagierDerivativeDifferenceForm = 0 := by
  apply levelSix_eq_zero_of_bounded_div_qParam_pow (k := 2) (n := 3) (by norm_num)
  let qmap : ℍ → ℂ := fun τ => qParam 1 τ
  have hq0 : Tendsto qmap atImInfty (𝓝 0) := by
    dsimp [qmap]
    exact ((qParam_tendsto (h := 1) (by norm_num)).comp tendsto_coe_atImInfty).mono_right
      nhdsWithin_le_nhds
  have hqpunct : Tendsto qmap atImInfty (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hq0, ?_⟩
    exact Filter.Eventually.of_forall (fun τ => by
      change qmap τ ≠ 0
      exact exp_ne_zero _)
  have hsmall : ∀ᶠ τ in atImInfty, ‖qmap τ‖ < 1 / 2 ^ 25 := by
    have hball : Metric.ball (0 : ℂ) (1 / 2 ^ 25) ∈ 𝓝 (0 : ℂ) :=
      Metric.ball_mem_nhds (0 : ℂ) (by norm_num)
    simpa [Metric.mem_ball, dist_zero_right] using hq0.eventually hball
  have hprod := tendsto_div_cube_zagierDerivativeDifferenceProduct.comp hqpunct
  have hbig : Asymptotics.IsBigO atImInfty
      (fun τ : ℍ => zagierDerivativeDifferenceProduct (qmap τ) / qmap τ ^ 3)
      (fun _ => (1 : ℝ)) := hprod.isBigO_one ℝ
  have heq : (fun τ : ℍ => zagierDerivativeDifferenceForm τ /
      qParam 1 τ ^ 3) =ᶠ[atImInfty]
      (fun τ : ℍ => zagierDerivativeDifferenceProduct (qmap τ) / qmap τ ^ 3) := by
    filter_upwards [hsmall] with τ hτ
    rw [zagierDerivativeDifferenceForm_eq_product hτ]
  have hbig' := hbig.congr' heq.symm (Filter.Eventually.of_forall (fun _ => rfl))
  change BoundedAtFilter atImInfty _
  simpa only [qmap] using hbig'

theorem zagier_modular_identity (τ : ℍ) :
    hauptmodulLogDerivativeForm τ =
      (1 - 10 * hauptmodulEta τ + 9 * hauptmodulEta τ ^ 2) * zagierEtaSquare τ := by
  have h := congrArg
    (fun f : ModularForm (CongruenceSubgroup.Gamma0 6) 2 => f τ)
    zagierDerivativeDifferenceForm_eq_zero
  simp only [ModularForm.zero_apply, zagierDerivativeDifferenceForm_apply] at h
  rw [hauptmodulLogDerivativeForm_apply]
  linear_combination h

end DirichletL

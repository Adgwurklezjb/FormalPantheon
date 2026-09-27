import Analysis.NumeratorProductAnalytic
import Analysis.NumeratorProductModularForms
import Analysis.ZagierEtaSeries
import Analysis.ZagierQSeriesTransfer

/-!
The full beta/gamma numerator product identities from CDT v2, Section 11.1,
and Zagier (2009), Sections 5-6. The exact order-seven bound proves that the
weight-six differences vanish. Analytic uniqueness and the linear coefficient
then give the unsquared integer-series identities.
-/

namespace DirichletL

open Complex Filter Function.Periodic
open _root_.UpperHalfPlane hiding I
open scoped Topology ModularForm

theorem zagierCaseCDAnalytic_ne_zero {q : ℂ} (hq : ‖q‖ < 1) :
    zagierCaseCDAnalytic q ≠ 0 := by
  have hq6 : ‖q ^ 6‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (by decide : 6 ≠ 0)
  exact mul_ne_zero (pow_ne_zero 6 (qEulerProduct_ne_zero hq))
    (pow_ne_zero 4 (qEulerProduct_ne_zero hq6))

theorem betaNumeratorSquareDifferenceForm_eq_quotient (τ : ℍ) :
    betaNumeratorSquareDifferenceForm τ =
      betaNumeratorClearedAnalytic (qParam 1 τ) / zagierCaseCDAnalytic (qParam 1 τ) ^ 3 := by
  have hD : zagierCaseCDAnalytic (qParam 1 τ) ≠ 0 :=
    zagierCaseCDAnalytic_ne_zero (by simpa using norm_qParam_lt_one 1 τ)
  rw [betaNumeratorSquareDifferenceForm_apply,
    hauptmodulEta_eq_product, zagierEtaSquare_eq_product]
  change betaNumeratorAnalytic (qParam 1 τ) ^ 2 -
    hauptmodulProduct (qParam 1 τ) ^ 2 *
      (1 - 10 * hauptmodulProduct (qParam 1 τ) +
        9 * hauptmodulProduct (qParam 1 τ) ^ 2) ^ 2 *
      (zagierCaseCNAnalytic (qParam 1 τ) / zagierCaseCDAnalytic (qParam 1 τ)) ^ 3 = _
  dsimp only [betaNumeratorClearedAnalytic]
  field_simp [hD]

theorem gammaNumeratorSquareDifferenceForm_eq_quotient (τ : ℍ) :
    gammaNumeratorSquareDifferenceForm τ =
      gammaNumeratorClearedAnalytic (qParam 1 τ) / zagierCaseCDAnalytic (qParam 1 τ) ^ 3 := by
  have hD : zagierCaseCDAnalytic (qParam 1 τ) ≠ 0 :=
    zagierCaseCDAnalytic_ne_zero (by simpa using norm_qParam_lt_one 1 τ)
  rw [gammaNumeratorSquareDifferenceForm_apply,
    hauptmodulEta_eq_product, zagierEtaSquare_eq_product]
  change gammaNumeratorAnalytic (qParam 1 τ) ^ 2 -
    hauptmodulProduct (qParam 1 τ) ^ 2 * (1 - 9 * hauptmodulProduct (qParam 1 τ)) ^ 2 *
      (zagierCaseCNAnalytic (qParam 1 τ) / zagierCaseCDAnalytic (qParam 1 τ)) ^ 3 = _
  dsimp only [gammaNumeratorClearedAnalytic]
  field_simp [hD]

private theorem weight_six_eq_zero_of_cleared_tendsto
    (f : ModularForm (CongruenceSubgroup.Gamma0 6) 6) {g : ℂ → ℂ} {c : ℂ}
    (ht : Tendsto (fun q : ℂ => g q / q ^ 7) (𝓝[≠] 0) (𝓝 c))
    (he : ∀ τ : ℍ, f τ = g (qParam 1 τ) / zagierCaseCDAnalytic (qParam 1 τ) ^ 3) :
    f = 0 := by
  apply levelSix_eq_zero_of_bounded_div_qParam_pow (k := 6) (n := 7) (by norm_num)
  have hD : Tendsto zagierCaseCDAnalytic (𝓝[≠] 0) (𝓝 1) := by
    have hD0 : zagierCaseCDAnalytic 0 = 1 := by
      simp [zagierCaseCDAnalytic, qEulerProduct_zero]
    rw [← hD0]
    exact hasFPowerSeriesAt_zagierCaseCDAnalytic.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hlim : Tendsto (fun q : ℂ => (g q / zagierCaseCDAnalytic q ^ 3) / q ^ 7)
      (𝓝[≠] 0) (𝓝 c) := by
    convert ht.div (hD.pow 3) (by norm_num : (1 ^ 3 : ℂ) ≠ 0) using 1
    · ext q
      dsimp only [Pi.div_apply]
      ring
    · simp
  have hq0 : Tendsto (fun τ : ℍ => qParam 1 τ) atImInfty (𝓝 0) :=
    ((qParam_tendsto (h := 1) (by norm_num)).comp tendsto_coe_atImInfty).mono_right
      nhdsWithin_le_nhds
  have hq : Tendsto (fun τ : ℍ => qParam 1 τ) atImInfty (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hq0, Filter.Eventually.of_forall (fun _ => exp_ne_zero _)⟩
  have hb := (hlim.comp hq).isBigO_one ℝ
  change BoundedAtFilter atImInfty _
  exact hb.congr' (Filter.Eventually.of_forall (fun τ => by
    change g (qParam 1 τ) / zagierCaseCDAnalytic (qParam 1 τ) ^ 3 / qParam 1 τ ^ 7 =
      f τ / qParam 1 τ ^ 7
    rw [he τ]))
    (Filter.Eventually.of_forall (fun _ => rfl))

theorem betaNumeratorSquareDifferenceForm_eq_zero :
    betaNumeratorSquareDifferenceForm = 0 :=
  weight_six_eq_zero_of_cleared_tendsto betaNumeratorSquareDifferenceForm
    tendsto_div_seventh_betaNumeratorClearedAnalytic
    betaNumeratorSquareDifferenceForm_eq_quotient

theorem gammaNumeratorSquareDifferenceForm_eq_zero :
    gammaNumeratorSquareDifferenceForm = 0 :=
  weight_six_eq_zero_of_cleared_tendsto gammaNumeratorSquareDifferenceForm
    tendsto_div_seventh_gammaNumeratorClearedAnalytic
    gammaNumeratorSquareDifferenceForm_eq_quotient

private theorem cleared_series_eq_zero {p : PowerSeries ℤ} {g : ℂ → ℂ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 6) 6)
    (hp : HasFPowerSeriesAt g (complexSeries (PowerSeries.map (Int.castRingHom ℚ) p)) 0)
    (hg0 : g 0 = 0) (hf : f = 0)
    (he : ∀ τ : ℍ, f τ = g (qParam 1 τ) / zagierCaseCDAnalytic (qParam 1 τ) ^ 3) :
    p = 0 := by
  have hg : g =ᶠ[𝓝 (0 : ℂ)] (fun _ => 0) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq
    by_cases hq0 : q = 0
    · simpa only [hq0] using hg0
    have hq1 : ‖q‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hq
    let τ : ℍ := ⟨invQParam 1 q, invQParam_one_im_pos hq0 hq1⟩
    have hqp : qParam 1 (τ : ℂ) = q := qParam_right_inv (by norm_num) hq0
    have h := he τ
    rw [hf, ModularForm.zero_apply, hqp] at h
    exact (div_eq_zero_iff.mp h.symm).resolve_right
      (pow_ne_zero 3 (zagierCaseCDAnalytic_ne_zero hq1))
  have h := hp.eq_zero_of_eventually hg
  ext n
  have hn := congrArg (fun s : FormalMultilinearSeries ℂ ℂ ℂ => s.coeff n) h
  dsimp only at hn
  have hz : (0 : FormalMultilinearSeries ℂ ℂ ℂ).coeff n = 0 := by
    simp [FormalMultilinearSeries.coeff]
  rw [hz] at hn
  have hc : (PowerSeries.coeff (R := ℤ) n p : ℂ) = 0 := by
    simpa [coeff_complexSeries, PowerSeries.coeff_map] using hn
  have hi : PowerSeries.coeff (R := ℤ) n p = 0 := by exact_mod_cast hc
  simpa only [map_zero] using hi

theorem betaNumeratorClearedSeries_eq_zero : betaNumeratorClearedSeries = 0 := by
  apply cleared_series_eq_zero betaNumeratorSquareDifferenceForm
    hasFPowerSeriesAt_betaNumeratorClearedAnalytic ?_
    betaNumeratorSquareDifferenceForm_eq_zero betaNumeratorSquareDifferenceForm_eq_quotient
  have hb : betaNumeratorAnalytic 0 = 0 := by
    calc
      _ = ∑' _ : ℕ, (0 : ℂ) := by
        apply tsum_congr
        intro n
        cases n with
        | zero => simp [betaNumerator]
        | succ n => simp
      _ = 0 := tsum_zero
  simp [betaNumeratorClearedAnalytic, hb, hauptmodulProduct]

theorem gammaNumeratorClearedSeries_eq_zero : gammaNumeratorClearedSeries = 0 := by
  apply cleared_series_eq_zero gammaNumeratorSquareDifferenceForm
    hasFPowerSeriesAt_gammaNumeratorClearedAnalytic ?_
    gammaNumeratorSquareDifferenceForm_eq_zero gammaNumeratorSquareDifferenceForm_eq_quotient
  have hg : gammaNumeratorAnalytic 0 = 0 := by
    calc
      _ = ∑' _ : ℕ, (0 : ℂ) := by
        apply tsum_congr
        intro n
        cases n with
        | zero => simp [gammaNumerator]
        | succ n => simp
      _ = 0 := tsum_zero
  simp [gammaNumeratorClearedAnalytic, hg, hauptmodulProduct]

private theorem numerator_eq_product_of_cleared_eq_zero (a : ℕ → ℤ) (P : PowerSeries ℤ)
    (ha : a 1 = 1) (hP : PowerSeries.constantCoeff (R := ℤ) P = 1)
    (h : (PowerSeries.mk a) ^ 2 * zagierCaseCD ^ 3 -
      hauptmodul ^ 2 * P ^ 2 * zagierCaseCN ^ 3 = 0) :
    PowerSeries.mk a = hauptmodul * P * zagierEtaSeries ^ 3 := by
  have hs : (PowerSeries.mk a) ^ 2 = (hauptmodul * P * zagierEtaSeries ^ 3) ^ 2 := by
    apply mul_right_cancel₀ (pow_ne_zero 3 zagierCaseCD_ne_zero)
    calc
      _ = hauptmodul ^ 2 * P ^ 2 * zagierCaseCN ^ 3 := sub_eq_zero.mp h
      _ = _ := by rw [zagierCaseCN_eq_etaSeries_sq_mul]; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hpos | hneg
  · exact hpos
  have hprod : PowerSeries.coeff (R := ℤ) 1 (hauptmodul * P * zagierEtaSeries ^ 3) = 1 := by
    simp [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_eq_map, Finset.sum_map,
      Finset.sum_range_succ, constantCoeff_hauptmodul, coeff_one_hauptmodul,
      hP, constantCoeff_zagierEtaSeries]
  have hc := congrArg (PowerSeries.coeff (R := ℤ) 1) hneg
  simp only [PowerSeries.coeff_mk, map_neg, ha, hprod] at hc
  norm_num at hc

theorem betaNumerator_product_identity :
    PowerSeries.mk betaNumerator =
      hauptmodul * (1 - 10 * hauptmodul + 9 * hauptmodul ^ 2) * zagierEtaSeries ^ 3 := by
  apply numerator_eq_product_of_cleared_eq_zero betaNumerator _ betaNumerator_one
    ?_ betaNumeratorClearedSeries_eq_zero
  simp [constantCoeff_hauptmodul]

theorem gammaNumerator_product_identity :
    PowerSeries.mk gammaNumerator =
      hauptmodul * (1 - 9 * hauptmodul) * zagierEtaSeries ^ 3 := by
  apply numerator_eq_product_of_cleared_eq_zero gammaNumerator _ (by decide)
    ?_ gammaNumeratorClearedSeries_eq_zero
  simp [constantCoeff_hauptmodul]

end DirichletL

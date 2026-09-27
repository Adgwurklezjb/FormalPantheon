import Analysis.MobiusTrace
import Analysis.ZagierAnalytic

/-!
Local analytic descent in CDT v2, Lemma `etalecover` and Definition `defG`.
The estimates below apply to the previously constructed formal descent.
-/

namespace DirichletL

open Filter
open scoped Topology NNReal ENNReal

private theorem sum_norm_trace_terms_le (f : PowerSeries ℚ) {M A : ℝ}
    (hM : 0 ≤ M) (hA : 1 ≤ A)
    (hf : ∀ k : ℕ, ‖(PowerSeries.coeff (R := ℚ) k f : ℂ)‖ ≤ M * A ^ k)
    (y : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n + 1),
      ‖(PowerSeries.coeff (R := ℚ) k f : ℂ) * ((mobiusTracePolynomial k).coeff n : ℂ) * y ^ n‖) ≤
        2 * M * (2 * n + 1) * (4 * A ^ 2 * ‖y‖) ^ n := by
  have hbase : 1 ≤ 2 * A := by linarith
  have hpow : (2 * A) ^ (2 * n) = (4 * A ^ 2) ^ n := by
    rw [pow_mul]
    congr 1
    ring
  calc
    _ ≤ ∑ _k ∈ Finset.range (2 * n + 1), 2 * M * (4 * A ^ 2 * ‖y‖) ^ n := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ 2 * n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [norm_mul, norm_mul, norm_pow]
      calc
        _ ≤ (M * A ^ k) * 2 ^ (k + 1) * ‖y‖ ^ n := by
          gcongr
          · exact hf k
          · exact norm_coeff_mobiusTracePolynomial k n
        _ = 2 * M * (2 * A) ^ k * ‖y‖ ^ n := by
          rw [pow_succ, mul_pow]
          ring
        _ ≤ 2 * M * (2 * A) ^ (2 * n) * ‖y‖ ^ n := by
          gcongr
          exact hbase
        _ = 2 * M * (4 * A ^ 2 * ‖y‖) ^ n := by rw [hpow, mul_pow]; ring
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- Polynomial times geometric growth controls every descended coefficient. -/
theorem norm_coeff_symmetrizedDescent_le (f : PowerSeries ℚ) {M A : ℝ}
    (hM : 0 ≤ M) (hA : 1 ≤ A)
    (hf : ∀ k : ℕ, ‖(PowerSeries.coeff (R := ℚ) k f : ℂ)‖ ≤ M * A ^ k) (n : ℕ) :
    ‖(PowerSeries.coeff (R := ℚ) n (symmetrizedDescent f) : ℂ)‖ ≤
      2 * M * (2 * n + 1) * (4 * A ^ 2) ^ n := by
  rw [coeff_symmetrizedDescent_eq_sum, Rat.cast_sum]
  calc
    _ ≤ ∑ k ∈ Finset.range (2 * n + 1),
        ‖(PowerSeries.coeff (R := ℚ) k f : ℂ) * ((mobiusTracePolynomial k).coeff n : ℂ)‖ := by
      simpa only [Rat.cast_mul] using norm_sum_le
        (Finset.range (2 * n + 1))
        (fun k => ((PowerSeries.coeff (R := ℚ) k f * (mobiusTracePolynomial k).coeff n : ℚ) : ℂ))
    _ ≤ _ := by simpa using sum_norm_trace_terms_le f hM hA hf 1 n

private theorem summable_trace_majorant {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1) (M : ℝ) :
    Summable (fun n : ℕ => 2 * M * (2 * n + 1) * q ^ n) := by
  have h0 := summable_geometric_of_lt_one hq0 hq
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using hq)
  convert ((h1.mul_left 2).add h0).mul_left (2 * M) using 1
  ext n
  simp only [pow_one]
  ring

/-- The trace double series is absolutely convergent near the invariant-coordinate origin. -/
theorem summable_norm_mobiusTrace (f : PowerSeries ℚ) {M A : ℝ}
    (hM : 0 ≤ M) (hA : 1 ≤ A)
    (hf : ∀ k : ℕ, ‖(PowerSeries.coeff (R := ℚ) k f : ℂ)‖ ≤ M * A ^ k)
    {y : ℂ} (hy : 4 * A ^ 2 * ‖y‖ < 1) :
    Summable (fun p : ℕ × ℕ =>
      ‖(PowerSeries.coeff (R := ℚ) p.2 f : ℂ) *
        ((mobiusTracePolynomial p.2).coeff p.1 : ℂ) * y ^ p.1‖) := by
  have hcol (n : ℕ) : HasSum
      (fun k : ℕ => ‖(PowerSeries.coeff (R := ℚ) k f : ℂ) *
        ((mobiusTracePolynomial k).coeff n : ℂ) * y ^ n‖)
      (∑ k ∈ Finset.range (2 * n + 1), ‖(PowerSeries.coeff (R := ℚ) k f : ℂ) *
        ((mobiusTracePolynomial k).coeff n : ℂ) * y ^ n‖) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hnk : 2 * n < k := by simpa using hk
    rw [coeff_mobiusTracePolynomial_eq_zero_of_lt hnk]
    simp
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun n => (hcol n).summable, ?_⟩
  apply Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => norm_nonneg _))
    (fun n => ?_) (summable_trace_majorant (by positivity) hy M)
  rw [(hcol n).tsum_eq]
  exact sum_norm_trace_terms_le f hM hA hf y n

/-- The analytic sum of the same descended series used in the denominator proofs. -/
noncomputable def symmetrizedAnalytic (f : PowerSeries ℚ) : ℂ → ℂ :=
  (complexSeries (symmetrizedDescent f)).sum

theorem symmetrizedAnalytic_eq_tsum (f : PowerSeries ℚ) (y : ℂ) :
    symmetrizedAnalytic f y =
      ∑' n : ℕ, (PowerSeries.coeff (R := ℚ) n (symmetrizedDescent f) : ℂ) * y ^ n := by
  change FormalMultilinearSeries.ofScalarsSum
    (fun n => (PowerSeries.coeff (R := ℚ) n (symmetrizedDescent f) : ℂ)) y = _
  simp [FormalMultilinearSeries.ofScalars_sum_eq]

private theorem hasSum_mobiusTracePolynomial (k : ℕ) (y : ℂ) :
    HasSum (fun n : ℕ => ((mobiusTracePolynomial k).coeff n : ℂ) * y ^ n)
      (Polynomial.aeval y (mobiusTracePolynomial k)) := by
  have hdeg : (mobiusTracePolynomial k).natDegree < k + 1 := by
    apply Nat.lt_succ_of_le
    exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      (fun n hn => coeff_mobiusTracePolynomial_eq_zero_of_gt hn)
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range' (algebraMap ℚ ℂ) hdeg y]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  have hkn : k < n := by simpa using hn
  rw [coeff_mobiusTracePolynomial_eq_zero_of_gt hkn]
  simp

set_option maxHeartbeats 400000 in
/-- Absolute convergence realizes the formal trace formula as an analytic series. -/
theorem symmetrizedAnalytic_eq_tsum_trace (f : PowerSeries ℚ) {M A : ℝ}
    (hM : 0 ≤ M) (hA : 1 ≤ A)
    (hf : ∀ k : ℕ, ‖(PowerSeries.coeff (R := ℚ) k f : ℂ)‖ ≤ M * A ^ k)
    {y : ℂ} (hy : 4 * A ^ 2 * ‖y‖ < 1) :
    symmetrizedAnalytic f y = ∑' k : ℕ,
      (PowerSeries.coeff (R := ℚ) k f : ℂ) * Polynomial.aeval y (mobiusTracePolynomial k) := by
  have hs := (summable_norm_mobiusTrace f hM hA hf hy).of_norm
  rw [symmetrizedAnalytic_eq_tsum]
  calc
    _ = ∑' n : ℕ, ∑' k : ℕ, (PowerSeries.coeff (R := ℚ) k f : ℂ) *
        ((mobiusTracePolynomial k).coeff n : ℂ) * y ^ n := by
      apply tsum_congr
      intro n
      rw [tsum_eq_sum (s := Finset.range (2 * n + 1))]
      · rw [coeff_symmetrizedDescent_eq_sum, Rat.cast_sum, Finset.sum_mul]
        simp only [Rat.cast_mul]
      · intro k hk
        have hnk : 2 * n < k := by simpa using hk
        rw [coeff_mobiusTracePolynomial_eq_zero_of_lt hnk]
        simp
    _ = ∑' k : ℕ, ∑' n : ℕ, (PowerSeries.coeff (R := ℚ) k f : ℂ) *
        ((mobiusTracePolynomial k).coeff n : ℂ) * y ^ n := hs.tsum_comm.symm
    _ = _ := by
      apply tsum_congr
      intro k
      simpa only [mul_assoc] using
        ((hasSum_mobiusTracePolynomial k y).mul_left (PowerSeries.coeff (R := ℚ) k f : ℂ)).tsum_eq

theorem le_radius_complexSeries_symmetrizedDescent (f : PowerSeries ℚ) {M A : ℝ}
    (hM : 0 ≤ M) (hA : 1 ≤ A)
    (hf : ∀ k : ℕ, ‖(PowerSeries.coeff (R := ℚ) k f : ℂ)‖ ≤ M * A ^ k)
    (r : ℝ≥0) (hr : 4 * A ^ 2 * (r : ℝ) < 1) :
    (r : ℝ≥0∞) ≤ (complexSeries (symmetrizedDescent f)).radius := by
  apply (complexSeries (symmetrizedDescent f)).le_radius_of_summable
  simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef, coeff_complexSeries]
  apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_trace_majorant (by positivity) hr M)
  calc
    _ ≤ (2 * M * (2 * n + 1) * (4 * A ^ 2) ^ n) * (r : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right (norm_coeff_symmetrizedDescent_le f hM hA hf n)
        (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- A positive geometric bound supplies a complex expansion of the descended series. -/
theorem hasFPowerSeriesOnBall_symmetrizedAnalytic (f : PowerSeries ℚ) {M A : ℝ}
    (hM : 0 ≤ M) (hA : 1 ≤ A)
    (hf : ∀ k : ℕ, ‖(PowerSeries.coeff (R := ℚ) k f : ℂ)‖ ≤ M * A ^ k)
    (r : ℝ≥0) (hr0 : 0 < r) (hr : 4 * A ^ 2 * (r : ℝ) < 1) :
    HasFPowerSeriesOnBall (symmetrizedAnalytic f)
      (complexSeries (symmetrizedDescent f)) 0 (r : ℝ≥0∞) := by
  have hrad := le_radius_complexSeries_symmetrizedDescent f hM hA hf r hr
  have hpos : (0 : ℝ≥0∞) < r := by exact_mod_cast hr0
  exact ((complexSeries (symmetrizedDescent f)).hasFPowerSeriesOnBall
    (hpos.trans_le hrad)).mono hpos hrad

private theorem summable_complexSeries_of_bound (f : PowerSeries ℚ) {M A : ℝ}
    (hA : 1 ≤ A)
    (hf : ∀ k : ℕ, ‖(PowerSeries.coeff (R := ℚ) k f : ℂ)‖ ≤ M * A ^ k)
    {x : ℂ} (hx : A * ‖x‖ < 1) :
    Summable (fun k : ℕ => (PowerSeries.coeff (R := ℚ) k f : ℂ) * x ^ k) := by
  apply Summable.of_norm_bounded (g := fun k => M * (A * ‖x‖) ^ k)
    ((summable_geometric_of_lt_one (by positivity) hx).mul_left M)
  intro k
  rw [norm_mul, norm_pow, mul_pow, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hf k) (by positivity)

/-- The convergent descended sum is the trace over the two coordinate roots. -/
theorem symmetrizedAnalytic_eq_sum_roots (f : PowerSeries ℚ) {M A : ℝ}
    (hM : 0 ≤ M) (hA : 1 ≤ A)
    (hf : ∀ k : ℕ, ‖(PowerSeries.coeff (R := ℚ) k f : ℂ)‖ ≤ M * A ^ k)
    {x w : ℂ} (hroot : x + w = x * w)
    (hx : A * ‖x‖ < 1) (hw : A * ‖w‖ < 1)
    (hy : 4 * A ^ 2 * ‖x + w‖ < 1) :
    symmetrizedAnalytic f (x + w) = (complexSeries f).sum x + (complexSeries f).sum w := by
  rw [symmetrizedAnalytic_eq_tsum_trace f hM hA hf hy]
  simp only [mobiusTracePolynomial_aeval x w hroot, mul_add]
  rw [(summable_complexSeries_of_bound f hA hf hx).tsum_add
    (summable_complexSeries_of_bound f hA hf hw)]
  have hsum (z : ℂ) : (complexSeries f).sum z =
      ∑' k : ℕ, (PowerSeries.coeff (R := ℚ) k f : ℂ) * z ^ k := by
    change FormalMultilinearSeries.ofScalarsSum (fun k => (PowerSeries.coeff (R := ℚ) k f : ℂ)) z = _
    simp [FormalMultilinearSeries.ofScalars_sum_eq]
  rw [hsum, hsum]

/-- The analytic pullback identity for positive symmetrization holds near zero. -/
theorem symmetrizedAnalytic_pullback (f : PowerSeries ℚ) {M A : ℝ}
    (hM : 0 ≤ M) (hA : 1 ≤ A)
    (hf : ∀ k : ℕ, ‖(PowerSeries.coeff (R := ℚ) k f : ℂ)‖ ≤ M * A ^ k) :
    (fun x : ℂ => symmetrizedAnalytic f (x + x / (x - 1))) =ᶠ[𝓝 0]
      (fun x => (complexSeries f).sum x + (complexSeries f).sum (x / (x - 1))) := by
  have hw : ContinuousAt (fun x : ℂ => x / (x - 1)) 0 :=
    continuousAt_id.div (continuousAt_id.sub continuousAt_const) (by norm_num)
  have hx : ContinuousAt (fun x : ℂ => A * ‖x‖) 0 :=
    continuousAt_const.mul continuousAt_id.norm
  have hw' : ContinuousAt (fun x : ℂ => A * ‖x / (x - 1)‖) 0 :=
    continuousAt_const.mul hw.norm
  have hy : ContinuousAt (fun x : ℂ => 4 * A ^ 2 * ‖x + x / (x - 1)‖) 0 :=
    continuousAt_const.mul (continuousAt_id.add hw).norm
  have hxb := hx.eventually_lt_const (by simp : A * ‖(0 : ℂ)‖ < 1)
  have hwb := hw'.eventually_lt_const (by simp : A * ‖(0 : ℂ) / (0 - 1)‖ < 1)
  have hyb := hy.eventually_lt_const
    (by simp : 4 * A ^ 2 * ‖(0 : ℂ) + 0 / (0 - 1)‖ < 1)
  filter_upwards [hxb, hwb, hyb] with x hx hw hy
  have hx1 : x ≠ 1 := by
    intro heq
    rw [heq, norm_one, mul_one] at hx
    linarith
  apply symmetrizedAnalytic_eq_sum_roots f hM hA hf _ hx hw hy
  field_simp [sub_ne_zero.mpr hx1]
  ring

private theorem exists_geometric_bound_of_pos_radius (f : PowerSeries ℚ)
    (hr : 0 < (complexSeries f).radius) :
    ∃ M A : ℝ, 0 ≤ M ∧ 1 ≤ A ∧
      ∀ k : ℕ, ‖(PowerSeries.coeff (R := ℚ) k f : ℂ)‖ ≤ M * A ^ k := by
  obtain ⟨M, B, hM, hB, hf⟩ := (complexSeries f).le_mul_pow_of_radius_pos hr
  refine ⟨M, max 1 B, hM.le, le_max_left _ _, fun k => ?_⟩
  have hk : ‖(PowerSeries.coeff (R := ℚ) k f : ℂ)‖ ≤ M * B ^ k := by
    simpa only [FormalMultilinearSeries.norm_apply_eq_norm_coef, coeff_complexSeries] using hf k
  exact hk.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hB.le (le_max_right _ _) k) hM.le)

/-- Positive input radius suffices for the formal positive descent to converge locally. -/
theorem pos_radius_complexSeries_symmetrizedDescent (f : PowerSeries ℚ)
    (hr : 0 < (complexSeries f).radius) :
    0 < (complexSeries (symmetrizedDescent f)).radius := by
  obtain ⟨M, A, hM, hA, hf⟩ := exists_geometric_bound_of_pos_radius f hr
  let r : ℝ≥0 := ⟨1 / (8 * A ^ 2), by positivity⟩
  have hr0 : (0 : ℝ≥0∞) < r := by
    rw [ENNReal.coe_pos]
    change (0 : ℝ) < 1 / (8 * A ^ 2)
    positivity
  apply hr0.trans_le (le_radius_complexSeries_symmetrizedDescent f hM hA hf r ?_)
  change 4 * A ^ 2 * (1 / (8 * A ^ 2)) < 1
  have hval : 4 * A ^ 2 * (1 / (8 * A ^ 2)) = (1 : ℝ) / 2 := by
    field_simp
    ring
  rw [hval]
  norm_num

theorem analyticAt_symmetrizedAnalytic_of_pos_radius (f : PowerSeries ℚ)
    (hr : 0 < (complexSeries f).radius) : AnalyticAt ℂ (symmetrizedAnalytic f) 0 := by
  exact ((complexSeries (symmetrizedDescent f)).hasFPowerSeriesOnBall
    (pos_radius_complexSeries_symmetrizedDescent f hr)).hasFPowerSeriesAt.analyticAt

/-- CDT's local positive analytic descent, with convergence as the only input hypothesis. -/
theorem symmetrizedAnalytic_pullback_of_pos_radius (f : PowerSeries ℚ)
    (hr : 0 < (complexSeries f).radius) :
    (fun x : ℂ => symmetrizedAnalytic f (x + x / (x - 1))) =ᶠ[𝓝 0]
      (fun x => (complexSeries f).sum x + (complexSeries f).sum (x / (x - 1))) := by
  obtain ⟨M, A, hM, hA, hf⟩ := exists_geometric_bound_of_pos_radius f hr
  exact symmetrizedAnalytic_pullback f hM hA hf

private theorem norm_coeff_hA_le_nine_pow (k : ℕ) :
    ‖(PowerSeries.coeff (R := ℚ) k hA : ℂ)‖ ≤ (1 : ℝ) * 9 ^ k := by
  simp only [hA, zagierGenerating, generatingSeries, PowerSeries.coeff_mk,
    Rat.cast_natCast, Complex.norm_natCast, one_mul]
  exact_mod_cast zagierC_le_nine_pow k

/-- CDT's formal series `G_A` defines an analytic function near zero. -/
theorem hasFPowerSeriesOnBall_symmetrizedAnalytic_hA :
    HasFPowerSeriesOnBall (symmetrizedAnalytic hA)
      (complexSeries (symmetrizedDescent hA)) 0 (1 / 648 : ℝ≥0∞) := by
  simpa using hasFPowerSeriesOnBall_symmetrizedAnalytic hA
    (M := 1) (A := 9) (by norm_num) (by norm_num) norm_coeff_hA_le_nine_pow
    (1 / 648 : ℝ≥0) (by norm_num) (by norm_num)

theorem analyticAt_symmetrizedAnalytic_hA {y : ℂ} (hy : ‖y‖ < 1 / 648) :
    AnalyticAt ℂ (symmetrizedAnalytic hA) y := by
  apply hasFPowerSeriesOnBall_symmetrizedAnalytic_hA.analyticAt_of_mem
  rw [EMetric.mem_ball, edist_zero_right, ← ofReal_norm_eq_enorm]
  have hr : ENNReal.ofReal (1 / 648 : ℝ) = (1 / 648 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  rw [← hr]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 648)).mpr hy

theorem symmetrizedAnalytic_hA_zero : symmetrizedAnalytic hA 0 = 2 := by
  have h := hasFPowerSeriesOnBall_symmetrizedAnalytic_hA.coeff_zero (fun _ => 1)
  simpa [FormalMultilinearSeries.apply_eq_pow_smul_coeff, coeff_complexSeries,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_symmetrizedDescent_hA]
    using h.symm

theorem deriv_symmetrizedAnalytic_hA_zero : deriv (symmetrizedAnalytic hA) 0 = -27 := by
  have h := hasFPowerSeriesOnBall_symmetrizedAnalytic_hA.hasFPowerSeriesAt.deriv
  simpa [FormalMultilinearSeries.apply_eq_pow_smul_coeff, coeff_complexSeries,
    coeff_one_symmetrizedDescent_hA] using h

/-- The analytic `G_A` in CDT Definition `defG` is the trace of the analytic `H_A`. -/
theorem symmetrizedAnalytic_hA_pullback :
    (fun x : ℂ => symmetrizedAnalytic hA (x + x / (x - 1))) =ᶠ[𝓝 0]
      (fun x => zagierAnalytic x + zagierAnalytic (x / (x - 1))) := by
  exact symmetrizedAnalytic_pullback hA (M := 1) (A := 9)
    (by norm_num) (by norm_num) norm_coeff_hA_le_nine_pow

end DirichletL

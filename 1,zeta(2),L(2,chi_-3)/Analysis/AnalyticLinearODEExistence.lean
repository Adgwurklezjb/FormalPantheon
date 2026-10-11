import Analysis.AnalyticLinearODECoefficients

/-!
Local analytic existence for complex linear matrix equations, supporting the
solution-space construction in CDT v2, Lemma `14functions`, before `explicitode`.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix NNReal ENNReal

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {I : Type*} [Fintype I]

/-- The absolutely convergent Cauchy product for matrix-vector multiplication. -/
theorem hasSum_matrix_mulVec_cauchy {a : ℕ → Matrix I I ℂ} {b : ℕ → I → ℂ}
    {a0 : Matrix I I ℂ} {b0 : I → ℂ} (ha : HasSum a a0) (hb : HasSum b b0)
    (han : Summable fun n => ‖a n‖) (hbn : Summable fun n => ‖b n‖) :
    HasSum (fun n => ∑ k ∈ Finset.range (n + 1), a k *ᵥ b (n - k)) (a0 *ᵥ b0) := by
  classical
  apply Pi.hasSum.mpr
  intro i
  have hprod (j : I) : HasSum
      (fun n => ∑ k ∈ Finset.range (n + 1), a k i j * b (n - k) j) (a0 i j * b0 j) := by
    have haij : HasSum (fun n => a n i j) (a0 i j) := Pi.hasSum.mp (Pi.hasSum.mp ha i) j
    have hbj : HasSum (fun n => b n j) (b0 j) := Pi.hasSum.mp hb j
    have hanij : Summable fun n => ‖a n i j‖ :=
      han.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun n => (norm_le_pi_norm (a n i) j).trans (norm_le_pi_norm (a n) i))
    have hbnj : Summable fun n => ‖b n j‖ :=
      hbn.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_le_pi_norm (b n) j)
    simpa only [haij.tsum_eq, hbj.tsum_eq] using
      hasSum_sum_range_mul_of_summable_norm hanij hbnj
  have hs := hasSum_sum (s := Finset.univ) (fun j _ => hprod j)
  convert hs using 1
  funext n
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct]
  exact Finset.sum_comm

/-- The convergent recurrence solution has the required actual complex derivative. -/
theorem hasDerivAt_matrixODESeries {A : ℂ → Matrix I I ℂ} {f : ℂ → I → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ (Matrix I I ℂ)} {v : I → ℂ}
    {z0 z : ℂ} {r s : ℝ≥0∞} (hA : HasFPowerSeriesOnBall A p z0 r)
    (hf : HasFPowerSeriesOnBall f (matrixODESeries p.coeff v) z0 s)
    (hzA : z ∈ EMetric.ball z0 r) (hzf : z ∈ EMetric.ball z0 s) :
    HasDerivAt f (A z *ᵥ f z) z := by
  let q := matrixODESeries p.coeff v
  let ev := ContinuousLinearMap.apply ℂ (I → ℂ) (1 : ℂ)
  have hd : HasFPowerSeriesOnBall (deriv f)
      (ev.compFormalMultilinearSeries q.derivSeries) z0 s :=
    ev.comp_hasFPowerSeriesOnBall hf.fderiv
  have hdc (n : ℕ) : (ev.compFormalMultilinearSeries q.derivSeries).coeff n =
      ((n + 1 : ℕ) : ℂ) • matrixODECoeff p.coeff v (n + 1) := by
    change q.derivSeries.coeff n 1 = _
    rw [FormalMultilinearSeries.derivSeries_coeff_one]
    simp only [q, coeff_matrixODESeries, Nat.cast_smul_eq_nsmul]
  have hdSum : HasSum
      (fun n => (z - z0) ^ n • (((n + 1 : ℕ) : ℂ) • matrixODECoeff p.coeff v (n + 1)))
      (deriv f z) := by
    simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, hdc] using hd.hasSum_sub hzf
  have hAr : z - z0 ∈ EMetric.ball 0 p.radius := by
    exact EMetric.ball_subset_ball hA.r_le (by simpa [edist_eq_enorm_sub] using hzA)
  have hfr : z - z0 ∈ EMetric.ball 0 q.radius := by
    exact EMetric.ball_subset_ball hf.r_le (by simpa [edist_eq_enorm_sub] using hzf)
  have hc := hasSum_matrix_mulVec_cauchy (hA.hasSum_sub hzA) (hf.hasSum_sub hzf)
    (p.summable_norm_apply hAr) (q.summable_norm_apply hfr)
  have hc' : HasSum
      (fun n => (z - z0) ^ n • (((n + 1 : ℕ) : ℂ) • matrixODECoeff p.coeff v (n + 1)))
      (A z *ᵥ f z) := by
    convert hc using 1
    funext n
    rw [succ_smul_matrixODECoeff, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff, coeff_matrixODESeries,
      Matrix.smul_mulVec_assoc, Matrix.mulVec_smul, smul_smul, ← pow_add,
      Nat.add_sub_of_le hk']
  rw [← hdSum.unique hc']
  exact (hf.analyticAt_of_mem hzf).differentiableAt.hasDerivAt

/-- Every initial vector has a local complex analytic solution of an analytic matrix ODE. -/
theorem exists_analytic_matrix_ode {A : ℂ → Matrix I I ℂ} {z0 : ℂ}
    (hA : AnalyticAt ℂ A z0) (v : I → ℂ) :
    ∃ f : ℂ → I → ℂ, AnalyticAt ℂ f z0 ∧ f z0 = v ∧
      ∀ᶠ z in 𝓝 z0, HasDerivAt f (A z *ᵥ f z) z := by
  obtain ⟨p, r, hp⟩ := hA
  obtain ⟨M, R, hM, hR, hbound⟩ := p.le_mul_pow_of_radius_pos hp.radius_pos
  let q := matrixODESeries p.coeff v
  have hq : 0 < q.radius := matrixODESeries_radius_pos v hM hR
    (fun n => by simpa only [FormalMultilinearSeries.norm_apply_eq_norm_coef] using hbound n)
  let f : ℂ → I → ℂ := fun z => q.sum (z - z0)
  have hf : HasFPowerSeriesOnBall f q z0 q.radius := by
    simpa only [zero_add] using (q.hasFPowerSeriesOnBall hq).comp_sub z0
  refine ⟨f, hf.analyticAt, ?_, ?_⟩
  · have h0 := hf.coeff_zero (1 : Fin 0 → ℂ)
    change q.coeff 0 = f z0 at h0
    simpa only [q, coeff_matrixODESeries,
      matrixODECoeff_zero] using h0.symm
  · filter_upwards [EMetric.ball_mem_nhds z0 hp.r_pos,
      EMetric.ball_mem_nhds z0 hq] with z hzA hzf
    exact hasDerivAt_matrixODESeries hp hf hzA hzf

end DirichletL

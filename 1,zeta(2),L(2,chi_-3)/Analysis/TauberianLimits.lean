import Analysis.TauberianFourier

/-!
Boundary limits for the Wiener-Ikehara route to CDT v2's lcm input
(supplied TeX 3291-3310). Based on the PrimeNumberTheoremAnd contributors,
Wiener.lean at revision 0766218b21b11ddf24103352ece7f0cb730945e0,
lines 910-1020 and 1049-1067. Original source and Apache 2.0 license
L-series terms, Schwartz integrability, and compact rectangle bounds.
-/

namespace DirichletL

open MeasureTheory Filter Set
open scoped Topology FourierTransform SchwartzMap

theorem tendsto_tsum_tauberianFourierTerm_boundary {f : ℕ → ℂ} {C : ℝ}
    (hsum : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ C * n) {x : ℝ} (hx : 0 < x)
    (ψ : 𝓢(ℝ, ℂ)) :
    Tendsto (fun σ : ℝ => ∑' n, LSeries.term f (σ : ℂ) n *
      𝓕 ψ (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x))) (𝓝[>] 1)
      (𝓝 (∑' n, tauberianFourierTerm f ψ x n)) := by
  apply tendsto_tsum_of_dominated_convergence
    ((summable_norm_mul_tauberianWeight hsum hx).mul_left (tauberianFourierSize ψ))
  · intro n
    change Tendsto (fun σ : ℝ => LSeries.term f (σ : ℂ) n * _)
      (𝓝[>] 1) (𝓝 ((f n / (n : ℂ)) * _))
    apply Tendsto.mul_const
    by_cases hn : n = 0
    · simp [hn]
    simp only [LSeries.term_of_ne_zero hn]
    have hσ : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝 1) :=
      (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    simpa only [Complex.cpow_one] using tendsto_const_nhds.div
      (hσ.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn))) (by simpa using hn)
  · apply eventually_nhdsWithin_of_forall
    intro σ hσ n
    calc
      ‖LSeries.term f (σ : ℂ) n *
          𝓕 ψ (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x))‖ ≤
          ‖LSeries.term f 1 n *
            𝓕 ψ (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x))‖ := by
        simp only [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (LSeries.norm_term_le_of_re_le_re f (by simpa using hσ.le) n) (norm_nonneg _)
      _ = ‖tauberianFourierTerm f ψ x n‖ := by
        rw [LSeries.term_of_ne_zero' one_ne_zero, Complex.cpow_one]
        rfl
      _ ≤ _ := norm_tauberianFourierTerm_le f ψ x n

theorem tendsto_tauberian_pole_integral (A : ℂ) (ψ : 𝓢(ℝ, ℂ)) {x : ℝ} (hx : 1 ≤ x) :
    Tendsto (fun σ : ℝ => A * ((x ^ (1 - σ) : ℝ) : ℂ) *
      ∫ u in Ici (-Real.log x), (Real.exp (-u * (σ - 1)) : ℂ) *
        𝓕 ψ (u / (2 * Real.pi))) (𝓝[>] 1)
      (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 ψ (u / (2 * Real.pi)))) := by
  apply Tendsto.mul
  · have hσ : Tendsto (fun σ : ℝ => 1 - σ) (𝓝[>] 1) (𝓝 0) := by
      simpa using ((continuous_id.tendsto (1 : ℝ)).mono_left
        nhdsWithin_le_nhds).const_sub (1 : ℝ)
    have hp : Tendsto (fun σ : ℝ => x ^ (1 - σ)) (𝓝[>] 1) (𝓝 1) := by
      simpa using tendsto_const_nhds.rpow hσ (Or.inl (zero_lt_one.trans_le hx).ne')
    simpa using ((Complex.continuous_ofReal.tendsto 1).comp hp).const_mul A
  · apply tendsto_integral_filter_of_dominated_convergence
      (fun u : ℝ => x * ‖𝓕 ψ (u / (2 * Real.pi))‖)
    · apply Eventually.of_forall
      intro σ
      have hF : Continuous (𝓕 ψ) := (SchwartzMap.fourierTransformCLM ℂ ψ).continuous
      apply Continuous.aestronglyMeasurable
      fun_prop
    · apply eventually_of_mem (Ioo_mem_nhdsGT_of_mem (show (1 : ℝ) ∈ Ico 1 2 by norm_num))
      intro σ hσ
      rw [ae_restrict_iff' measurableSet_Ici]
      apply Eventually.of_forall
      intro u hu
      have hu' : -Real.log x ≤ u := hu
      have he : Real.exp (-u * (σ - 1)) ≤ x := by
        calc
          Real.exp (-u * (σ - 1)) ≤ Real.exp (Real.log x * (σ - 1)) :=
            Real.exp_monotone (mul_le_mul_of_nonneg_right (by linarith [hu'])
              (by linarith [hσ.1]))
          _ ≤ Real.exp (Real.log x) := Real.exp_monotone
            (by nlinarith [Real.log_nonneg hx, hσ.2])
          _ = x := Real.exp_log (zero_lt_one.trans_le hx)
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)] using mul_le_mul_of_nonneg_right he
          (norm_nonneg (𝓕 ψ (u / (2 * Real.pi))))
    · exact (((SchwartzMap.fourierTransformCLM ℂ ψ).integrable.comp_div
        (by positivity)).norm.const_mul x).integrableOn
    · apply Eventually.of_forall
      intro u
      have he : Continuous (fun σ : ℝ => (Real.exp (-u * (σ - 1)) : ℂ)) := by fun_prop
      simpa using (he.tendsto 1).mul_const (𝓕 ψ (u / (2 * Real.pi))) |>.mono_left
        nhdsWithin_le_nhds

theorem tendsto_tauberian_boundary_integral {G : ℂ → ℂ}
    (hG : ContinuousOn G {s | 1 ≤ s.re}) (ψ : 𝓢(ℝ, ℂ))
    (hψ : HasCompactSupport (ψ : ℝ → ℂ)) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun σ : ℝ => ∫ t : ℝ, G ((σ : ℂ) + (t : ℂ) * Complex.I) * ψ t *
      (x : ℂ) ^ ((t : ℂ) * Complex.I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + (t : ℂ) * Complex.I) * ψ t *
        (x : ℂ) ^ ((t : ℂ) * Complex.I))) := by
  let K : Set ℂ := Complex.reProdIm (Icc 1 2) (tsupport (ψ : ℝ → ℂ))
  have hK : IsCompact K := isCompact_Icc.reProdIm hψ
  have hKG : K ⊆ {s : ℂ | 1 ≤ s.re} := fun _ hs => (Complex.mem_reProdIm.mp hs).1.1
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hG.mono hKG)
  have hpow : Continuous (fun t : ℝ => (x : ℂ) ^ ((t : ℂ) * Complex.I)) :=
    (show Continuous (fun t : ℝ => (t : ℂ) * Complex.I) by fun_prop).const_cpow
      (Or.inl (by exact_mod_cast hx.ne'))
  apply tendsto_integral_filter_of_dominated_convergence (fun t => M * ‖ψ t‖)
  · apply eventually_of_mem (Icc_mem_nhdsGT_of_mem (show (1 : ℝ) ∈ Ico 1 2 by norm_num))
    intro σ hσ
    exact (((hG.comp_continuous (by fun_prop) (by simp [hσ.1])).mul ψ.continuous).mul
      hpow).aestronglyMeasurable
  · apply eventually_of_mem (Icc_mem_nhdsGT_of_mem (show (1 : ℝ) ∈ Ico 1 2 by norm_num))
    intro σ hσ
    apply Eventually.of_forall
    intro t
    by_cases ht : t ∈ tsupport (ψ : ℝ → ℂ)
    · have hmem : (σ : ℂ) + (t : ℂ) * Complex.I ∈ K := by
        simp [K, Complex.mem_reProdIm, hσ.1, hσ.2, ht]
      have hpn : ‖(x : ℂ) ^ ((t : ℂ) * Complex.I)‖ = 1 := by
        simp [Complex.norm_cpow_of_ne_zero (show (x : ℂ) ≠ 0 by simpa using hx.ne'),
          Complex.arg_ofReal_of_nonneg hx.le]
      simp only [norm_mul, hpn, mul_one]
      exact mul_le_mul_of_nonneg_right (hM _ hmem) (norm_nonneg _)
    · have hn : t ∉ Function.support (ψ : ℝ → ℂ) :=
        fun hs => ht (subset_tsupport (ψ : ℝ → ℂ) hs)
      have hz : ψ t = 0 := by simpa using hn
      simp [hz]
  · exact ψ.integrable.norm.const_mul M
  · apply Eventually.of_forall
    intro t
    apply Tendsto.mul_const
    apply Tendsto.mul_const
    refine (hG (1 + (t : ℂ) * Complex.I) (by simp)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩)
    · exact ((Complex.continuous_ofReal.tendsto 1).add tendsto_const_nhds).mono_left
        nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun σ (hσ : 1 < σ) => by simp [hσ.le])

theorem tendsto_integral_cpow_imaginary (h : ℝ → ℂ) :
    Tendsto (fun x : ℝ => ∫ t : ℝ, h t * (x : ℂ) ^ ((t : ℂ) * Complex.I)) atTop (𝓝 0) := by
  have he : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ,
      (x : ℂ) ^ ((t : ℂ) * Complex.I) =
        Complex.exp ((Real.log x : ℂ) * (t : ℂ) * Complex.I) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx t
    rw [Complex.cpow_def_of_ne_zero (by simpa using hx.ne'), Complex.ofReal_log hx.le]
    ring_nf
  have hi : ∀ᶠ x : ℝ in atTop,
      (∫ t : ℝ, h t * (x : ℂ) ^ ((t : ℂ) * Complex.I)) =
        ∫ t : ℝ, h t * Complex.exp ((Real.log x : ℂ) * (t : ℂ) * Complex.I) := by
    filter_upwards [he] with x hx
    exact integral_congr_ae (Eventually.of_forall (fun t => by simp only [hx t]))
  rw [tendsto_congr' hi]
  convert_to Tendsto (fun x : ℝ => 𝓕 h (-Real.log x / (2 * Real.pi))) atTop (𝓝 0)
  · ext x
    rw [Real.fourierIntegral_eq']
    apply integral_congr_ae
    apply Eventually.of_forall
    intro t
    simp only [RCLike.inner_apply', conj_trivial, smul_eq_mul]
    rw [mul_comm (h t)]
    congr 1
    congr 1
    push_cast
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  refine (Real.zero_at_infty_fourierIntegral h).comp
    (Tendsto.mono_right ?_ atBot_le_cocompact)
  exact (tendsto_neg_atBot_iff.mpr Real.tendsto_log_atTop).atBot_mul_const
    (inv_pos.mpr Real.two_pi_pos)

end DirichletL

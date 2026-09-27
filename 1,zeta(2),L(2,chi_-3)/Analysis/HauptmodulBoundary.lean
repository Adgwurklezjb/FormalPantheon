import Analysis.HauptmodulFricke

/-!
The real interval and cusp-zero boundary value in CDT v2, Section 11.1,
equation `haupt`. The declaration and endpoint checks are recorded in
-/

namespace DirichletL

open Complex Filter Function.Periodic
open scoped Topology Real

theorem hauptmodulProduct_ofReal_eq_fricke {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    hauptmodulProduct (q : ℂ) =
      hauptmodulFrickeProduct (Real.exp (2 * π ^ 2 / (3 * Real.log q)) : ℂ) := by
  let τ : ℂ := (-(Real.log q) / (2 * π) : ℝ) * I
  let σ : ℂ := (-π / (3 * Real.log q) : ℝ) * I
  have hlog : Real.log q < 0 := Real.log_neg hq0 hq1
  have hπ0 : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hl0 : (Real.log q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hlog.ne
  have hσ : 0 < σ.im := by
    simp only [σ, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, zero_mul, add_zero]
    exact div_pos_of_neg_of_neg (neg_neg_of_pos Real.pi_pos)
      (mul_neg_of_pos_of_neg (by norm_num) hlog)
  have hfr : -1 / (6 * σ) = τ := by
    dsimp only [σ, τ]
    push_cast
    field_simp [hπ0, hl0, I_ne_zero]
    ring_nf
    norm_num
  have hqτ : qParam 1 τ = (q : ℂ) := by
    simp only [qParam, ofReal_one, div_one]
    have he : 2 * (π : ℂ) * I * τ = (Real.log q : ℂ) := by
      dsimp only [τ]
      push_cast
      field_simp [hπ0]
      ring_nf
      norm_num
    rw [he, ← ofReal_exp, Real.exp_log hq0]
  have hqσ : qParam 1 σ = (Real.exp (2 * π ^ 2 / (3 * Real.log q)) : ℂ) := by
    simp only [qParam, ofReal_one, div_one, ofReal_exp]
    congr 1
    dsimp only [σ]
    push_cast
    field_simp [hl0]
    ring_nf
    norm_num
  calc
    hauptmodulProduct (q : ℂ) = hauptmodulEta τ := by
      rw [hauptmodulEta_eq_product, hqτ]
    _ = hauptmodulEta (-1 / (6 * σ)) := by rw [hfr]
    _ = hauptmodulFrickeProduct (qParam 1 σ) := hauptmodulEta_fricke_eq_product hσ
    _ = _ := by rw [hqσ]

theorem hauptmodulProduct_ofReal_mem {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    hauptmodulProduct (q : ℂ) ∈ Complex.ofReal '' Set.Ioo (0 : ℝ) (1 / 9) := by
  rw [hauptmodulProduct_ofReal_eq_fricke hq0 hq1]
  apply hauptmodulFrickeProduct_ofReal_mem (Real.exp_pos _)
  apply Real.exp_lt_one_iff.mpr
  exact div_neg_of_pos_of_neg (by positivity)
    (mul_neg_of_pos_of_neg (by norm_num) (Real.log_neg hq0 hq1))

theorem tendsto_hauptmodulProduct_ofReal_nhdsLT_one :
    Tendsto (fun q : ℝ => hauptmodulProduct (q : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 (1 / 9 : ℂ)) := by
  have hpos : ∀ᶠ q : ℝ in 𝓝[<] 1, 0 < q :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ q : ℝ in 𝓝[<] 1, q < 1 := self_mem_nhdsWithin
  have hl : Tendsto Real.log (𝓝[<] (1 : ℝ)) (𝓝[<] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Real.log_one] using
        (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    · filter_upwards [hpos, hlt] with q hq0 hq1
      exact Real.log_neg hq0 hq1
  have hi := (tendsto_inv_zero_atBot.comp hl).const_mul_atBot
    (by positivity : (0 : ℝ) < 2 * π ^ 2 / 3)
  have he : Tendsto (fun q : ℝ => Real.exp (2 * π ^ 2 / (3 * Real.log q)))
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    convert Real.tendsto_exp_atBot.comp hi using 1
    funext q
    congr 1
    simp only [Function.comp_apply]
    ring
  have hec : Tendsto (fun q : ℝ => (Real.exp (2 * π ^ 2 / (3 * Real.log q)) : ℂ))
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    simpa only [ofReal_zero] using continuous_ofReal.continuousAt.tendsto.comp he
  have hF := continuousAt_hauptmodulFrickeProduct_zero.tendsto.comp hec
  rw [hauptmodulFrickeProduct_zero] at hF
  apply hF.congr'
  filter_upwards [hpos, hlt] with q hq0 hq1
  exact (hauptmodulProduct_ofReal_eq_fricke hq0 hq1).symm

theorem differentiableOn_hauptmodulProduct :
    DifferentiableOn ℂ hauptmodulProduct (Metric.ball 0 1) := by
  have hp (d : ℕ) (hd : 0 < d) :
      DifferentiableOn ℂ (fun q : ℂ => qEulerProduct (q ^ d)) (Metric.ball 0 1) := by
    apply DifferentiableOn.comp (g := qEulerProduct) (f := fun q : ℂ => q ^ d)
      differentiableOn_qEulerProduct (differentiable_id.pow d).differentiableOn
    intro q hq
    simpa only [Metric.mem_ball, dist_zero_right, norm_pow] using
      pow_lt_one₀ (norm_nonneg q) (by simpa using hq) hd.ne'
  have hn (d : ℕ) (hd : 0 < d) {q : ℂ} (hq : q ∈ Metric.ball 0 1) :
      qEulerProduct (q ^ d) ≠ 0 := by
    apply qEulerProduct_ne_zero
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) (by simpa using hq) hd.ne'
  exact ((differentiableOn_id.mul (differentiableOn_qEulerProduct.pow 4)).mul
    ((hp 6 (by norm_num)).pow 8)).div
      (((hp 2 (by norm_num)).pow 8).mul ((hp 3 (by norm_num)).pow 4))
      (fun q hq => mul_ne_zero (pow_ne_zero _ (hn 2 (by norm_num) hq))
        (pow_ne_zero _ (hn 3 (by norm_num) hq)))

end DirichletL

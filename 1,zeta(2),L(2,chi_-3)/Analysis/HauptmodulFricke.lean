import Analysis.HauptmodulModular
import Analysis.QEulerProductReal

/-!
Eta inversion and real product bounds at the cusp zero in CDT v2,
Section 11.1, equation `haupt`. The exact factor is 1/9. See
-/

namespace DirichletL

open Complex Filter Function.Periodic
open scoped Topology Real

/-- The Euler product obtained from the Hauptmodul by inversion at level six. -/
noncomputable def hauptmodulFrickeProduct (q : ℂ) : ℂ :=
  (1 / 9) * qEulerProduct q ^ 8 * qEulerProduct (q ^ 6) ^ 4 /
    (qEulerProduct (q ^ 2) ^ 4 * qEulerProduct (q ^ 3) ^ 8)

@[simp] theorem hauptmodulFrickeProduct_zero : hauptmodulFrickeProduct 0 = 1 / 9 := by
  norm_num [hauptmodulFrickeProduct]

private theorem eta_neg_inv_even_pow {τ : ℂ} (hτ : 0 < τ.im) (k : ℕ) :
    dedekindEta (-1 / τ) ^ (2 * k) = (-I * τ) ^ k * dedekindEta τ ^ (2 * k) := by
  have hs : ((-I * τ) ^ (1 / 2 : ℂ)) ^ 2 = -I * τ := by
    simpa only [one_div] using cpow_nat_inv_pow (-I * τ) (n := 2) two_ne_zero
  have he := congrArg (fun z : ℂ => z ^ 2) (dedekindEta_neg_inv hτ)
  dsimp only at he
  rw [mul_pow, hs] at he
  simpa only [mul_pow, pow_mul] using congrArg (fun z : ℂ => z ^ k) he

theorem hauptmodulEta_fricke_eq_product {τ : ℂ} (hτ : 0 < τ.im) :
    hauptmodulEta (-1 / (6 * τ)) = hauptmodulFrickeProduct (qParam 1 τ) := by
  have hτ0 : τ ≠ 0 := fun h => (ne_of_gt hτ) (congrArg Complex.im h)
  have h2 : 0 < (2 * τ).im := by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hτ
  have h3 : 0 < (3 * τ).im := by simpa using mul_pos (by norm_num : (0 : ℝ) < 3) hτ
  have h6 : 0 < (6 * τ).im := by simpa using mul_pos (by norm_num : (0 : ℝ) < 6) hτ
  have harg6 : (6 : ℂ) * (-1 / (6 * τ)) = -1 / τ := by field_simp
  have harg2 : (2 : ℂ) * (-1 / (6 * τ)) = -1 / (3 * τ) := by field_simp; ring
  have harg3 : (3 : ℂ) * (-1 / (6 * τ)) = -1 / (2 * τ) := by field_simp; ring
  have hscale : ((-I * (6 * τ)) ^ 2 * (-I * τ) ^ 4) /
      ((-I * (3 * τ)) ^ 4 * (-I * (2 * τ)) ^ 2) = (1 / 9 : ℂ) := by
    apply (div_eq_iff (mul_ne_zero
      (pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr I_ne_zero)
        (mul_ne_zero (by norm_num : (3 : ℂ) ≠ 0) hτ0)))
      (pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr I_ne_zero)
        (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hτ0))))).mpr
    ring
  have htransform : hauptmodulEta (-1 / (6 * τ)) =
      (1 / 9 : ℂ) * dedekindEta τ ^ 8 * dedekindEta (6 * τ) ^ 4 /
        (dedekindEta (2 * τ) ^ 4 * dedekindEta (3 * τ) ^ 8) := by
    rw [hauptmodulEta, harg6, harg2, harg3,
      eta_neg_inv_even_pow h6 2, eta_neg_inv_even_pow hτ 4,
      eta_neg_inv_even_pow h3 4, eta_neg_inv_even_pow h2 2]
    calc
      _ = (((-I * (6 * τ)) ^ 2 * (-I * τ) ^ 4) /
          ((-I * (3 * τ)) ^ 4 * (-I * (2 * τ)) ^ 2)) *
            (dedekindEta τ ^ 8 * dedekindEta (6 * τ) ^ 4 /
              (dedekindEta (2 * τ) ^ 4 * dedekindEta (3 * τ) ^ 8)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by rw [hscale]; ring
  rw [htransform]
  have hq2 := qParam_one_nat_mul 2 τ
  have hq3 := qParam_one_nat_mul 3 τ
  have hq6 := qParam_one_nat_mul 6 τ
  simp only [Nat.cast_ofNat] at hq2 hq3 hq6
  simp only [dedekindEta, mul_pow, hq2, hq3, hq6, hauptmodulFrickeProduct]
  have he : exp (π * I * τ / 12) ^ 8 * exp (π * I * (6 * τ) / 12) ^ 4 /
      (exp (π * I * (2 * τ) / 12) ^ 4 * exp (π * I * (3 * τ) / 12) ^ 8) = 1 := by
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_nat_mul, ← exp_nat_mul,
      ← exp_add, ← exp_add, ← exp_sub]
    have hz : (8 : ℂ) * (π * I * τ / 12) + 4 * (π * I * (6 * τ) / 12) -
        (4 * (π * I * (2 * τ) / 12) + 8 * (π * I * (3 * τ) / 12)) = 0 := by ring
    simpa only [Nat.cast_ofNat, hz] using exp_zero
  calc
    _ = (exp (π * I * τ / 12) ^ 8 * exp (π * I * (6 * τ) / 12) ^ 4 /
        (exp (π * I * (2 * τ) / 12) ^ 4 * exp (π * I * (3 * τ) / 12) ^ 8)) *
          ((1 / 9) * qEulerProduct (qParam 1 τ) ^ 8 * qEulerProduct (qParam 1 τ ^ 6) ^ 4 /
            (qEulerProduct (qParam 1 τ ^ 2) ^ 4 * qEulerProduct (qParam 1 τ ^ 3) ^ 8)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [he, one_mul]

private theorem fricke_factor_mem_Ioo {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    ((1 - u + u ^ 2) / (1 + u + u ^ 2)) ^ 4 ∈ Set.Ioo (0 : ℝ) 1 := by
  have hn : 0 < 1 - u + u ^ 2 := by nlinarith [sq_nonneg u]
  have hd : 0 < 1 + u + u ^ 2 := by positivity
  have hr : 0 < (1 - u + u ^ 2) / (1 + u + u ^ 2) := div_pos hn hd
  exact ⟨pow_pos hr 4, pow_lt_one₀ hr.le ((div_lt_one hd).mpr (by linarith)) (by norm_num)⟩

private theorem hasProd_real_fricke_factors {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    HasProd (fun n : ℕ =>
      ((1 - q ^ (n + 1) + (q ^ (n + 1)) ^ 2) /
        (1 + q ^ (n + 1) + (q ^ (n + 1)) ^ 2)) ^ 4)
      ((∏' n : ℕ, (1 - q ^ (n + 1))) ^ 8 * (∏' n : ℕ, (1 - (q ^ 6) ^ (n + 1))) ^ 4 /
        ((∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) ^ 4 *
          (∏' n : ℕ, (1 - (q ^ 3) ^ (n + 1))) ^ 8)) := by
  have ht (d : ℕ) (hd : 0 < d) :
      Tendsto (fun s : Finset ℕ => ∏ n ∈ s, (1 - (q ^ d) ^ (n + 1))) atTop
        (𝓝 (∏' n : ℕ, (1 - (q ^ d) ^ (n + 1)))) :=
    (multipliable_real_qEulerProduct_factors (pow_nonneg hq0.le d)
      (pow_lt_one₀ hq0.le hq1 hd.ne')).hasProd
  have h1 : Tendsto (fun s : Finset ℕ => ∏ n ∈ s, (1 - q ^ (n + 1))) atTop
      (𝓝 (∏' n : ℕ, (1 - q ^ (n + 1)))) := by simpa only [pow_one] using ht 1 (by norm_num)
  have hEpos (d : ℕ) (hd : 0 < d) : 0 < ∏' n : ℕ, (1 - (q ^ d) ^ (n + 1)) :=
    real_qEulerProduct_pos (pow_nonneg hq0.le d) (pow_lt_one₀ hq0.le hq1 hd.ne')
  have hdiv := ((h1.pow 8).mul ((ht 6 (by norm_num)).pow 4)).div
    (((ht 2 (by norm_num)).pow 4).mul ((ht 3 (by norm_num)).pow 8))
      (mul_pos (pow_pos (hEpos 2 (by norm_num)) 4) (pow_pos (hEpos 3 (by norm_num)) 8)).ne'
  change Tendsto _ atTop _
  convert hdiv using 1
  funext s
  simp only [Pi.div_apply, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
    ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro n _
  have hp (d : ℕ) : (q ^ d) ^ (n + 1) = (q ^ (n + 1)) ^ d := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hp 6, hp 2, hp 3]
  let u := q ^ (n + 1)
  have hu0 : 0 < u := pow_pos hq0 _
  have hu1 : u < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
  have h2 : 1 - u ^ 2 ≠ 0 := (sub_pos.mpr (pow_lt_one₀ hu0.le hu1 (by norm_num))).ne'
  have h3 : 1 - u ^ 3 ≠ 0 := (sub_pos.mpr (pow_lt_one₀ hu0.le hu1 (by norm_num))).ne'
  have hd : 1 + u + u ^ 2 ≠ 0 := (show 0 < 1 + u + u ^ 2 by positivity).ne'
  have hb : (1 - u + u ^ 2) / (1 + u + u ^ 2) =
      (1 - u) ^ 2 * (1 - u ^ 6) / ((1 - u ^ 2) * (1 - u ^ 3) ^ 2) := by
    field_simp [h2, h3, hd]
    ring
  change ((1 - u + u ^ 2) / (1 + u + u ^ 2)) ^ 4 =
    (1 - u) ^ 8 * (1 - u ^ 6) ^ 4 / ((1 - u ^ 2) ^ 4 * (1 - u ^ 3) ^ 8)
  rw [hb, div_pow, mul_pow, mul_pow]
  simp only [← pow_mul]

theorem hauptmodulFrickeProduct_ofReal_mem {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    hauptmodulFrickeProduct (q : ℂ) ∈ Complex.ofReal '' Set.Ioo (0 : ℝ) (1 / 9) := by
  let E : ℝ → ℝ := fun r => ∏' n : ℕ, (1 - r ^ (n + 1))
  let Q := E q ^ 8 * E (q ^ 6) ^ 4 / (E (q ^ 2) ^ 4 * E (q ^ 3) ^ 8)
  let f : ℕ → ℝ := fun n =>
    ((1 - q ^ (n + 1) + (q ^ (n + 1)) ^ 2) /
      (1 + q ^ (n + 1) + (q ^ (n + 1)) ^ 2)) ^ 4
  have hEpos (d : ℕ) (hd : 0 < d) : 0 < E (q ^ d) :=
    real_qEulerProduct_pos (pow_nonneg hq0.le d) (pow_lt_one₀ hq0.le hq1 hd.ne')
  have hQpos : 0 < Q :=
    div_pos (mul_pos (pow_pos (real_qEulerProduct_pos hq0.le hq1) 8)
      (pow_pos (hEpos 6 (by norm_num)) 4))
      (mul_pos (pow_pos (hEpos 2 (by norm_num)) 4) (pow_pos (hEpos 3 (by norm_num)) 8))
  have hf (n : ℕ) : f n ∈ Set.Ioo (0 : ℝ) 1 :=
    fricke_factor_mem_Ioo (pow_pos hq0 _) (pow_lt_one₀ hq0.le hq1 (by omega))
  have hprod : HasProd f Q := hasProd_real_fricke_factors hq0 hq1
  have hupper : Q ≤ f 0 := by
    apply le_of_tendsto hprod.tendsto_prod_nat
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    cases n with
    | zero => omega
    | succ n =>
      rw [Finset.prod_range_succ']
      have ht : ∏ i ∈ Finset.range n, f (i + 1) ≤ 1 :=
        Finset.prod_le_one (fun i _ => (hf (i + 1)).1.le) (fun i _ => (hf (i + 1)).2.le)
      simpa only [one_mul, mul_comm] using mul_le_mul_of_nonneg_right ht (hf 0).1.le
  have hQlt : Q < 1 := hupper.trans_lt (hf 0).2
  refine ⟨Q / 9, ⟨div_pos hQpos (by norm_num), (div_lt_div_iff_of_pos_right (by norm_num)).mpr hQlt⟩, ?_⟩
  have hcast (d : ℕ) (hd : 0 < d) : qEulerProduct ((q : ℂ) ^ d) = (E (q ^ d) : ℂ) := by
    rw [← Complex.ofReal_pow]
    exact qEulerProduct_ofReal (pow_nonneg hq0.le d) (pow_lt_one₀ hq0.le hq1 hd.ne')
  rw [hauptmodulFrickeProduct, qEulerProduct_ofReal hq0.le hq1,
    hcast 6 (by norm_num), hcast 2 (by norm_num), hcast 3 (by norm_num)]
  dsimp only [Q, E]
  push_cast
  ring

theorem continuousAt_hauptmodulFrickeProduct_zero : ContinuousAt hauptmodulFrickeProduct 0 := by
  have hE : ContinuousAt qEulerProduct 0 :=
    (differentiableOn_qEulerProduct.differentiableAt (Metric.ball_mem_nhds _ (by norm_num))).continuousAt
  have hp (d : ℕ) (hd : 0 < d) : ContinuousAt (fun q : ℂ => qEulerProduct (q ^ d)) 0 := by
    apply ContinuousAt.comp (g := qEulerProduct) (f := fun q : ℂ => q ^ d)
    · simpa only [zero_pow (by omega : d ≠ 0)] using hE
    · exact continuousAt_id.pow d
  have hnum : ContinuousAt (fun q : ℂ => (1 / 9 : ℂ) * qEulerProduct q ^ 8 *
      qEulerProduct (q ^ 6) ^ 4) 0 :=
    (continuousAt_const.mul (hE.pow 8)).mul ((hp 6 (by norm_num)).pow 4)
  have hden : ContinuousAt (fun q : ℂ => qEulerProduct (q ^ 2) ^ 4 *
      qEulerProduct (q ^ 3) ^ 8) 0 :=
    ((hp 2 (by norm_num)).pow 4).mul ((hp 3 (by norm_num)).pow 8)
  exact hnum.div hden (by simp)

end DirichletL

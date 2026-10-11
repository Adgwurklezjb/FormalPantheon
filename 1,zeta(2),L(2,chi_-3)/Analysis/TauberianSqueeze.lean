import Analysis.TauberianSmoothed
import Analysis.SmoothIntervalApproximation

/-!
Positive-sequence squeeze on the Wiener-Ikehara route to CDT v2,
Section 2.2 (supplied TeX 3291-3310). Based on the PrimeNumberTheoremAnd
contributors, Wiener.lean at revision 0766218b21b11ddf24103352ece7f0cb730945e0,
lines 1879-2190, archived with its Apache 2.0 license in
topology and exact natural ceiling bounds.
-/

namespace DirichletL

open MeasureTheory Filter Set
open scoped Topology ContDiff

theorem summable_mul_comp_div_of_hasCompactSupport {f : ℕ → ℝ} {g : ℝ → ℝ}
    (hg : HasCompactSupport g) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => f n * g ((n : ℝ) / x)) := by
  obtain ⟨M, hM⟩ := hg.bddAbove.mono (subset_tsupport g)
  apply summable_of_finite_support
  simp only [Function.support_mul]
  apply Finite.inter_of_right
  rw [finite_iff_bddAbove]
  exact ⟨Nat.ceil (M * x), fun n hn => by
    simpa using Nat.ceil_mono ((div_le_iff₀ hx).mp (hM hn))⟩

theorem tsum_mul_comp_div_mono {f : ℕ → ℝ} {g₁ g₂ : ℝ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hg : g₁ ≤ g₂) (hg₁ : HasCompactSupport g₁)
    (hg₂ : HasCompactSupport g₂) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, f n * g₁ ((n : ℝ) / x)) / x ≤
      (∑' n : ℕ, f n * g₂ ((n : ℝ) / x)) / x := by
  apply div_le_div_of_nonneg_right _ hx.le
  exact Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (hg _) (hf n))
    (summable_mul_comp_div_of_hasCompactSupport hg₁ hx)
    (summable_mul_comp_div_of_hasCompactSupport hg₂ hx)

theorem tendsto_tsum_mul_indicator_Ico {f : ℕ → ℝ} {C A : ℝ} {G : ℂ → ℂ}
    (hpos : ∀ n, 0 ≤ f n) (hA : 0 ≤ A)
    (hsum : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ C * n)
    (hf : ∀ σ : ℝ, 1 < σ → LSeriesSummable (fun n => (f n : ℂ)) (σ : ℂ))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : EqOn G (fun s => LSeries (fun n => (f n : ℂ)) s - (A : ℂ) / (s - 1))
      {s | 1 < s.re}) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun x : ℝ =>
      (∑' n : ℕ, f n * (Ico a b).indicator (1 : ℝ → ℝ) ((n : ℝ) / x)) / x)
      atTop (𝓝 (A * (b - a))) := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp
  let S (g : ℝ → ℝ) (x : ℝ) := (∑' n : ℕ, f n * g ((n : ℝ) / x)) / x
  let J : ℝ → ℝ := (Ico a b).indicator 1
  have hJ : HasCompactSupport J := by
    simpa [J, HasCompactSupport, tsupport, hab.ne] using
      (isCompact_Icc : IsCompact (Icc a b))
  change Tendsto (S J) atTop (𝓝 (A * (b - a)))
  rw [tendsto_order]
  constructor
  · intro q hq
    obtain ⟨ε, hε, hε'⟩ := exists_between
      (lt_min (show 0 < b - a by linarith)
        (div_pos (sub_pos.mpr hq) (show 0 < A + 1 by positivity)))
    have hεw := (lt_min_iff.mp hε').1
    have hsmall : ε * (A + 1) < A * (b - a) - q :=
      (lt_div_iff₀ (by positivity)).mp (lt_min_iff.mp hε').2
    obtain ⟨ψ, hsm, hs, hp, _, hle, hint⟩ :=
      exists_contDiff_le_indicator_Ico ha hε hεw
    have hlim : Tendsto (S ψ) atTop (𝓝 (A * ∫ y in Ioi (0 : ℝ), ψ y)) :=
      tendsto_tsum_mul_smoothed_real hsum hf hG hG' hsm hs hp
    have hq' : q < A * ∫ y in Ioi (0 : ℝ), ψ y := by
      have hm := mul_le_mul_of_nonneg_left hint hA
      nlinarith
    filter_upwards [eventually_gt_atTop (0 : ℝ), hlim.eventually (Ioi_mem_nhds hq')]
      with x hx hqx
    exact hqx.trans_le (tsum_mul_comp_div_mono hpos hle hs hJ hx)
  · intro q hq
    obtain ⟨ε, hε, hε'⟩ := exists_between
      (lt_min (show 0 < 2 * a by positivity)
        (div_pos (sub_pos.mpr hq) (show 0 < A + 1 by positivity)))
    have hεa := (lt_min_iff.mp hε').1
    have hsmall : ε * (A + 1) < q - A * (b - a) :=
      (lt_div_iff₀ (by positivity)).mp (lt_min_iff.mp hε').2
    obtain ⟨ψ, hsm, hs, hp, hle, _, hint⟩ :=
      exists_contDiff_indicator_Ico_le hab hε hεa
    have hlim : Tendsto (S ψ) atTop (𝓝 (A * ∫ y in Ioi (0 : ℝ), ψ y)) :=
      tendsto_tsum_mul_smoothed_real hsum hf hG hG' hsm hs hp
    have hq' : A * (∫ y in Ioi (0 : ℝ), ψ y) < q := by
      have hm := mul_le_mul_of_nonneg_left hint hA
      nlinarith
    filter_upwards [eventually_gt_atTop (0 : ℝ), hlim.eventually (Iio_mem_nhds hq')]
      with x hx hxq
    exact (tsum_mul_comp_div_mono hpos hle hJ hs hx).trans_lt hxq

theorem tsum_mul_indicator_Ico_eq_sum {f : ℕ → ℝ} {a b x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, f n * (Ico a b).indicator (1 : ℝ → ℝ) ((n : ℝ) / x)) =
      ∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n := by
  have hm (n : ℕ) : n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊ ↔ (n : ℝ) / x ∈ Ico a b := by
    rw [Finset.mem_Ico, Set.mem_Ico, Nat.ceil_le, Nat.lt_ceil,
      le_div_iff₀ hx, div_lt_iff₀ hx]
  have hz (n : ℕ) (hn : n ∉ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊) :
      f n * (Ico a b).indicator (1 : ℝ → ℝ) ((n : ℝ) / x) = 0 := by
    have hn' : (n : ℝ) / x ∉ Ico a b := fun h => hn ((hm n).mpr h)
    simp only [indicator_of_not_mem hn', mul_zero]
  rw [tsum_eq_sum hz]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [indicator_of_mem ((hm n).mp hn), Pi.one_apply, mul_one]

theorem tendsto_sum_Ico_div {f : ℕ → ℝ} {C A : ℝ} {G : ℂ → ℂ}
    (hpos : ∀ n, 0 ≤ f n) (hA : 0 ≤ A)
    (hsum : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ C * n)
    (hf : ∀ σ : ℝ, 1 < σ → LSeriesSummable (fun n => (f n : ℂ)) (σ : ℂ))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : EqOn G (fun s => LSeries (fun n => (f n : ℂ)) s - (A : ℂ) / (s - 1))
      {s | 1 < s.re}) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Ico ⌈a * N⌉₊ ⌈b * N⌉₊, f n) / (N : ℝ))
      atTop (𝓝 (A * (b - a))) := by
  have ht := (tendsto_tsum_mul_indicator_Ico hpos hA hsum hf hG hG' ha hab).comp
    tendsto_natCast_atTop_atTop
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  dsimp only [Function.comp_def]
  rw [tsum_mul_indicator_Ico_eq_sum (show 0 < (N : ℝ) by exact_mod_cast hN)]

theorem tendsto_sum_range_div_of_tendsto_sum_Ico {f : ℕ → ℝ} {C A : ℝ}
    (hpos : ∀ n, 0 ≤ f n) (hA : 0 ≤ A)
    (hsum : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ C * n)
    (hinterval : ∀ a : ℝ, 0 < a → a ≤ 1 →
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.Ico ⌈a * N⌉₊ N, f n) / (N : ℝ))
        atTop (𝓝 (A * (1 - a)))) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f n) / (N : ℝ)) atTop (𝓝 A) := by
  let T (N : ℕ) := (∑ n ∈ Finset.range N, f n) / (N : ℝ)
  let U (a : ℝ) (N : ℕ) := (∑ n ∈ Finset.Ico ⌈a * N⌉₊ N, f n) / (N : ℝ)
  have hC : 0 ≤ C := by
    have h : ‖f 0‖ ≤ C := by simpa using hsum 1
    exact (norm_nonneg _).trans h
  have hsum' (N : ℕ) : (∑ n ∈ Finset.range N, f n) ≤ C * N := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hpos _)] using hsum N
  have hbounds {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1) {N : ℕ} (hN : 0 < N) :
      U a N ≤ T N ∧ T N ≤ U a N + C * (a + 1 / (N : ℝ)) := by
    have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
    have hceil : ⌈a * N⌉₊ ≤ N := by
      rw [Nat.ceil_le]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ha' hNR.le
    have hsplit : T N = U a N + (∑ n ∈ Finset.range ⌈a * N⌉₊, f n) / (N : ℝ) := by
      dsimp only [T, U]
      rw [← Finset.sum_range_add_sum_Ico f hceil, add_div]
      ring
    have hearly : (∑ n ∈ Finset.range ⌈a * N⌉₊, f n) / (N : ℝ) ≤
        C * (a + 1 / (N : ℝ)) := by
      calc
        _ ≤ C * (⌈a * N⌉₊ : ℝ) / (N : ℝ) :=
          div_le_div_of_nonneg_right (hsum' _) hNR.le
        _ ≤ C * (a * N + 1) / (N : ℝ) := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Nat.ceil_lt_add_one (mul_nonneg ha.le hNR.le)).le hC) hNR.le
        _ = _ := by field_simp
    rw [hsplit]
    constructor
    · exact le_add_of_nonneg_right (div_nonneg (Finset.sum_nonneg (fun n _ => hpos n)) hNR.le)
    · exact add_le_add_left hearly _
  change Tendsto T atTop (𝓝 A)
  rw [tendsto_order]
  constructor
  · intro q hq
    obtain ⟨a, ha, ha'⟩ := exists_between
      (lt_min zero_lt_one (div_pos (sub_pos.mpr hq) (show 0 < A + 1 by positivity)))
    have ha1 : a ≤ 1 := (lt_min_iff.mp ha').1.le
    have hsmall : a * (A + 1) < A - q :=
      (lt_div_iff₀ (by positivity)).mp (lt_min_iff.mp ha').2
    have hq' : q < A * (1 - a) := by nlinarith
    have ht : Tendsto (U a) atTop (𝓝 (A * (1 - a))) := hinterval a ha ha1
    filter_upwards [eventually_gt_atTop (0 : ℕ), ht.eventually (Ioi_mem_nhds hq')]
      with N hN hqN
    exact hqN.trans_le (hbounds ha ha1 hN).1
  · intro q hq
    obtain ⟨a, ha, ha'⟩ := exists_between
      (lt_min zero_lt_one (div_pos (sub_pos.mpr hq) (show 0 < C + 1 by positivity)))
    have ha1 : a ≤ 1 := (lt_min_iff.mp ha').1.le
    have hsmall : a * (C + 1) < q - A :=
      (lt_div_iff₀ (by positivity)).mp (lt_min_iff.mp ha').2
    have hq' : A * (1 - a) + C * a < q := by nlinarith
    have hi : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def, one_div] using
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop :
          Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)))
    have ht : Tendsto (fun N : ℕ => U a N + C * (a + 1 / (N : ℝ))) atTop
        (𝓝 (A * (1 - a) + C * a)) := by
      simpa only [add_zero] using (hinterval a ha ha1).add ((hi.const_add a).const_mul C)
    filter_upwards [eventually_gt_atTop (0 : ℕ), ht.eventually (Iio_mem_nhds hq')]
      with N hN hNq
    exact (hbounds ha ha1 hN).2.trans_lt hNq

theorem tendsto_sum_range_div_of_tauberian {f : ℕ → ℝ} {C A : ℝ} {G : ℂ → ℂ}
    (hpos : ∀ n, 0 ≤ f n) (hA : 0 ≤ A)
    (hsum : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ C * n)
    (hf : ∀ σ : ℝ, 1 < σ → LSeriesSummable (fun n => (f n : ℂ)) (σ : ℂ))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : EqOn G (fun s => LSeries (fun n => (f n : ℂ)) s - (A : ℂ) / (s - 1))
      {s | 1 < s.re}) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f n) / (N : ℝ)) atTop (𝓝 A) := by
  apply tendsto_sum_range_div_of_tendsto_sum_Ico hpos hA hsum
  intro a ha ha1
  simpa only [one_mul, Nat.ceil_natCast] using
    (tendsto_sum_Ico_div hpos hA hsum hf hG hG' ha ha1)

end DirichletL

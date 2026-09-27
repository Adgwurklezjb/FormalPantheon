import Arithmetic.LcmIntervalQuotientLengths
import Arithmetic.LcmIntervalQuotientLog
import Arithmetic.VonMangoldtIntervals

/-!
Uniform harmonic bounds for the actual cutoff gcd quotient in CDT v2,
Section 2.2, supplied TeX 3363-3430, and its use at TeX 4260-4283.
Exact prime-power sums allow all cutoffs simultaneously, including endpoints.
-/

namespace DirichletL

open Filter
open scoped Topology ArithmeticFunction.vonMangoldt

theorem sum_cutoff_vonMangoldt_lcmIntervalGap_eq (n k c : ℕ) {a : ℕ} (ha : 0 < a) :
    (∑ q ∈ (lcmIntervalGap n k a).filter (fun q => c < q), Λ q) =
      ∑ q ∈ Finset.Ico (⌊max (c : ℝ) ((n : ℝ) / ((a : ℝ) + 1))⌋₊ + 1)
        ⌈((n - k : ℕ) : ℝ) / (a : ℝ)⌉₊, Λ q := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a from ha)
  have hv : ((n - k : ℕ) : ℝ) / (a : ℝ) ≤ (n : ℝ) :=
    (div_le_self (Nat.cast_nonneg _) haR).trans (by exact_mod_cast Nat.sub_le n k)
  have he : (lcmIntervalGap n k a).filter (fun q => c < q) =
      (Finset.range (n + 1)).filter (fun q : ℕ =>
        max (c : ℝ) ((n : ℝ) / ((a : ℝ) + 1)) < (q : ℝ) ∧
          (q : ℝ) < ((n - k : ℕ) : ℝ) / (a : ℝ)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_range, max_lt_iff]
    constructor
    · rintro ⟨hq, hc⟩
      have hr := (mem_lcmIntervalGap_iff_real ha).mp hq
      exact ⟨Nat.lt_succ_iff.mpr (mem_lcmIntervalGap.mp hq).1,
        ⟨by exact_mod_cast hc, hr.1⟩, hr.2⟩
    · rintro ⟨_, ⟨hc, hlo⟩, hhi⟩
      exact ⟨(mem_lcmIntervalGap_iff_real ha).mpr ⟨hlo, hhi⟩, by exact_mod_cast hc⟩
  rw [he]
  exact sum_vonMangoldt_Ioo_eq_Ico ((Nat.cast_nonneg c).trans (le_max_left _ _)) hv

theorem sum_vonMangoldt_cutoff_eq_sub {n c : ℕ} (hcn : c ≤ n) :
    (∑ q ∈ (Finset.range (n + 1)).filter (fun q => c < q), Λ q) =
      Real.log (lcmPrefix n : ℝ) - Real.log (lcmPrefix c : ℝ) := by
  have he : (Finset.range (n + 1)).filter (fun q => c < q) = Finset.Ico (c + 1) (n + 1) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [he, Finset.sum_Ico_eq_sub _ (Nat.add_le_add_right hcn 1),
    log_lcmPrefix_eq_sum_vonMangoldt, log_lcmPrefix_eq_sum_vonMangoldt]

theorem abs_log_lcmIntervalQuotient_sub_mainTerm_le {n k c : ℕ}
    (hk : 0 < k) (hkn : k ≤ n) (hcn : c ≤ n) {δ : ℝ}
    (hprefix : ∀ m ≤ n, |Real.log (lcmPrefix m : ℝ) - (m : ℝ)| ≤ δ)
    (hinterval : ∀ u v : ℝ, 0 ≤ u → v ≤ (n : ℝ) →
      |(∑ q ∈ Finset.Ico (⌊u⌋₊ + 1) ⌈v⌉₊, Λ q) - max (v - u) 0| ≤ δ) :
    |Real.log (lcmIntervalQuotient n k c : ℝ) - lcmIntervalQuotientMainTerm n k c| ≤
      (((n / k : ℕ) : ℝ) + 1) * δ := by
  let S := Finset.Icc 1 (n / k - 1)
  let U (a : ℕ) : ℝ := ∑ q ∈ (lcmIntervalGap n k a).filter (fun q => c < q), Λ q
  let V (a : ℕ) : ℝ := lcmIntervalQuotientGapLength n k c a
  let B : ℝ := (Real.log (lcmPrefix n : ℝ) - (n : ℝ)) -
    (Real.log (lcmPrefix c : ℝ) - (c : ℝ))
  have hU : Real.log (lcmIntervalQuotient n k c : ℝ) + (∑ a ∈ S, U a) =
      Real.log (lcmPrefix n : ℝ) - Real.log (lcmPrefix c : ℝ) :=
    (log_lcmIntervalQuotient_add_sum_gaps n k c hk).trans (sum_vonMangoldt_cutoff_eq_sub hcn)
  have hV : (∑ a ∈ S, V a) = (n : ℝ) - (c : ℝ) - lcmIntervalQuotientMainTerm n k c :=
    sum_lcmIntervalQuotientGap_lengths hk hkn hcn
  have hdiff : Real.log (lcmIntervalQuotient n k c : ℝ) - lcmIntervalQuotientMainTerm n k c =
      B - ∑ a ∈ S, (U a - V a) := by
    rw [Finset.sum_sub_distrib]
    dsimp only [B]
    linarith only [hU, hV]
  have hB : |B| ≤ δ + δ := by
    calc
      _ ≤ |Real.log (lcmPrefix n : ℝ) - (n : ℝ)| +
          |Real.log (lcmPrefix c : ℝ) - (c : ℝ)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (Real.log (lcmPrefix n : ℝ) - (n : ℝ)) 0
            (Real.log (lcmPrefix c : ℝ) - (c : ℝ))
      _ ≤ _ := add_le_add (hprefix n le_rfl) (hprefix c hcn)
  have hb (a : ℕ) (ha : a ∈ S) : |U a - V a| ≤ δ := by
    have ha' := (Finset.mem_Icc.mp ha).1
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha'
    have hv : ((n - k : ℕ) : ℝ) / (a : ℝ) ≤ (n : ℝ) :=
      (div_le_self (Nat.cast_nonneg _) haR).trans (by exact_mod_cast Nat.sub_le n k)
    dsimp only [U, V, lcmIntervalQuotientGapLength]
    rw [sum_cutoff_vonMangoldt_lcmIntervalGap_eq n k c ha']
    exact hinterval _ _ ((Nat.cast_nonneg c).trans (le_max_left _ _)) hv
  have hR : 1 ≤ n / k := Nat.div_pos hkn hk
  rw [hdiff]
  calc
    _ ≤ |B| + |∑ a ∈ S, (U a - V a)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le B 0 (∑ a ∈ S, (U a - V a))
    _ ≤ (δ + δ) + ∑ a ∈ S, δ := add_le_add hB
      ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hb))
    _ = _ := by
      simp only [S, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      rw [Nat.cast_sub hR, Nat.cast_one]
      ring

theorem eventually_abs_log_lcmIntervalQuotient_sub_mainTerm_le {γ₀ ε : ℝ}
    (hγ : 0 < γ₀) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k ≤ n, ∀ c ≤ n, γ₀ * (n : ℝ) ≤ (k : ℝ) →
      |Real.log (lcmIntervalQuotient n k c : ℝ) - lcmIntervalQuotientMainTerm n k c| ≤
        ε * (n : ℝ) := by
  let D : ℝ := (⌈1 / γ₀⌉₊ : ℝ) + 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hsmall : 0 < ε / D := div_pos hε hD
  filter_upwards [eventually_abs_initialSegment_sub_le tendsto_log_lcmPrefix_div hsmall,
    eventually_abs_sum_vonMangoldt_Ico_sub_le hsmall, eventually_gt_atTop (0 : ℕ)]
    with n hn hi hn0 k hkn c hcn hγk
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hkR : (0 : ℝ) < k := (mul_pos hγ hnR).trans_le hγk
  have hk : 0 < k := by exact_mod_cast hkR
  have hprefix : ∀ m ≤ n, |Real.log (lcmPrefix m : ℝ) - (m : ℝ)| ≤ (ε / D) * (n : ℝ) := by
    simpa only [one_mul] using hn
  have hbound := abs_log_lcmIntervalQuotient_sub_mainTerm_le hk hkn hcn hprefix hi
  have hratio : (n : ℝ) / (k : ℝ) ≤ 1 / γ₀ := by
    apply (div_le_div_iff₀ hkR hγ).mpr
    nlinarith
  have hquot : ((n / k : ℕ) : ℝ) + 1 ≤ D := by
    have hle : ((n / k : ℕ) : ℝ) ≤ 1 / γ₀ := Nat.cast_div_le.trans hratio
    have hceil := Nat.le_ceil (1 / γ₀)
    dsimp only [D]
    linarith
  calc
    _ ≤ (((n / k : ℕ) : ℝ) + 1) * ((ε / D) * (n : ℝ)) := hbound
    _ ≤ D * ((ε / D) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hquot (mul_nonneg hsmall.le hnR.le)
    _ = _ := by field_simp

end DirichletL

import Arithmetic.LcmInterval

/-!
The missing prime-power intervals in CDT v2 Section 2.2, supplied
TeX 3330-3359. Exact von Mangoldt weights retain all prime powers,
and strict multiple inequalities preserve both interval endpoints.
-/

namespace DirichletL

open scoped ArithmeticFunction.vonMangoldt

/-- Indices whose consecutive multiples straddle the entire integer interval. -/
def lcmIntervalGap (n k a : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun q => a * q < n - k ∧ n < (a + 1) * q)

theorem mem_lcmIntervalGap {n k a q : ℕ} :
    q ∈ lcmIntervalGap n k a ↔ q ≤ n ∧ a * q < n - k ∧ n < (a + 1) * q := by
  simp only [lcmIntervalGap, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

theorem lcmIntervalGap_index_eq_div {n k a q : ℕ} (hq : q ∈ lcmIntervalGap n k a) :
    a = n / q := by
  have h := mem_lcmIntervalGap.mp hq
  exact (Nat.div_eq_of_lt_le (h.2.1.le.trans (Nat.sub_le n k)) h.2.2).symm

theorem lcmIntervalGap_disjoint {n k a b : ℕ} (hab : a ≠ b) :
    Disjoint (lcmIntervalGap n k a) (lcmIntervalGap n k b) := by
  apply Finset.disjoint_left.mpr
  intro q hqa hqb
  exact hab ((lcmIntervalGap_index_eq_div hqa).trans (lcmIntervalGap_index_eq_div hqb).symm)

theorem lcmIntervalGap_width {n k a q : ℕ} (hq : q ∈ lcmIntervalGap n k a) :
    (a + 1) * k < n := by
  have h := mem_lcmIntervalGap.mp hq
  have hkn : k ≤ n := by omega
  have hkq : k < q := by nlinarith [Nat.sub_add_cancel hkn]
  have hmul := Nat.mul_le_mul_left a hkq.le
  nlinarith [Nat.sub_add_cancel hkn]

theorem lcmIntervalGap_index_le_div {n k a q : ℕ} (hk : 0 < k)
    (hq : q ∈ lcmIntervalGap n k a) : a ≤ n / k - 1 := by
  have h : a + 1 ≤ n / k :=
    (Nat.le_div_iff_mul_le hk).mpr (lcmIntervalGap_width hq).le
  omega

theorem not_dvd_lcmInterval_iff_mem_biUnion {q n k : ℕ} (hq : IsPrimePow q)
    (hqn : q ≤ n) (hk : 0 < k) :
    ¬q ∣ lcmInterval n k ↔
      q ∈ (Finset.Icc 1 (n / k - 1)).biUnion (lcmIntervalGap n k) := by
  rw [isPrimePow_not_dvd_lcmInterval_iff hq hqn]
  constructor
  · rintro ⟨a, ha, hlo, hhi⟩
    have hm := mem_lcmIntervalGap.mpr ⟨hqn, hlo, hhi⟩
    exact Finset.mem_biUnion.mpr
      ⟨a, Finset.mem_Icc.mpr ⟨ha, lcmIntervalGap_index_le_div hk hm⟩, hm⟩
  · intro hm
    obtain ⟨a, ha, hqa⟩ := Finset.mem_biUnion.mp hm
    exact ⟨a, (Finset.mem_Icc.mp ha).1, (mem_lcmIntervalGap.mp hqa).2⟩

theorem log_lcmInterval_add_sum_gaps (n k : ℕ) (hk : 0 < k) :
    Real.log (lcmInterval n k : ℝ) +
      (∑ a ∈ Finset.Icc 1 (n / k - 1), ∑ q ∈ lcmIntervalGap n k a, Λ q) =
        ∑ q ∈ Finset.range (n + 1), Λ q := by
  classical
  let S := (Finset.range (n + 1)).filter (fun q => ¬q ∣ lcmInterval n k)
  let U := (Finset.Icc 1 (n / k - 1)).biUnion (lcmIntervalGap n k)
  have he : S.filter (fun q => Λ q ≠ 0) = U.filter (fun q => Λ q ≠ 0) := by
    ext q
    simp only [S, Finset.mem_filter, Finset.mem_range,
      ArithmeticFunction.vonMangoldt_ne_zero_iff]
    constructor
    · rintro ⟨⟨hqn, hd⟩, hq⟩
      exact ⟨(not_dvd_lcmInterval_iff_mem_biUnion hq (Nat.lt_succ_iff.mp hqn) hk).mp hd, hq⟩
    · rintro ⟨hm, hq⟩
      have hqn : q ≤ n := by
        obtain ⟨a, _, hqa⟩ := Finset.mem_biUnion.mp hm
        exact (mem_lcmIntervalGap.mp hqa).1
      exact ⟨⟨Nat.lt_succ_iff.mpr hqn,
        (not_dvd_lcmInterval_iff_mem_biUnion hq hqn hk).mpr hm⟩, hq⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 (n / k - 1))) (lcmIntervalGap n k) := by
    intro a _ b _ hab
    exact lcmIntervalGap_disjoint hab
  have hs : (∑ q ∈ S, Λ q) =
      ∑ a ∈ Finset.Icc 1 (n / k - 1), ∑ q ∈ lcmIntervalGap n k a, Λ q := by
    calc
      _ = ∑ q ∈ S.filter (fun q => Λ q ≠ 0), Λ q := (Finset.sum_filter_ne_zero _).symm
      _ = ∑ q ∈ U.filter (fun q => Λ q ≠ 0), Λ q := by rw [he]
      _ = ∑ q ∈ U, Λ q := Finset.sum_filter_ne_zero _
      _ = _ := Finset.sum_biUnion hdisj
  have h := log_lcmInterval_add_sum_vonMangoldt n k
  change Real.log (lcmInterval n k : ℝ) + (∑ q ∈ S, Λ q) = _ at h
  rw [hs] at h
  exact h

theorem mem_lcmIntervalGap_iff_real {n k a q : ℕ} (ha : 0 < a) :
    q ∈ lcmIntervalGap n k a ↔
      (n : ℝ) / ((a : ℝ) + 1) < (q : ℝ) ∧ (q : ℝ) < ((n - k : ℕ) : ℝ) / (a : ℝ) := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  constructor
  · intro hq
    have h := mem_lcmIntervalGap.mp hq
    have hlo : (a : ℝ) * (q : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast h.2.1
    have hhi : (n : ℝ) < ((a : ℝ) + 1) * (q : ℝ) := by exact_mod_cast h.2.2
    constructor
    · apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith
    · apply (lt_div_iff₀ haR).mpr
      nlinarith
  · rintro ⟨hlo, hhi⟩
    have hloR : (n : ℝ) < ((a : ℝ) + 1) * (q : ℝ) := by
      have h := (div_lt_iff₀ (show 0 < (a : ℝ) + 1 by positivity)).mp hlo
      nlinarith
    have hhiR : (a : ℝ) * (q : ℝ) < ((n - k : ℕ) : ℝ) := by
      have h := (lt_div_iff₀ haR).mp hhi
      nlinarith
    have h₁ : n < (a + 1) * q := by exact_mod_cast hloR
    have h₂ : a * q < n - k := by exact_mod_cast hhiR
    have hqa : q ≤ a * q := by
      simpa only [one_mul] using Nat.mul_le_mul_right q (show 1 ≤ a from ha)
    exact mem_lcmIntervalGap.mpr ⟨hqa.trans (h₂.le.trans (Nat.sub_le n k)), h₂, h₁⟩

theorem lcmInterval_eq_lcmPrefix_of_half_le {n k : ℕ} (hnk : n ≤ 2 * k) :
    lcmInterval n k = lcmPrefix n := by
  apply Nat.dvd_antisymm (lcmInterval_dvd_lcmPrefix n k)
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p e hp hpe
  cases e with
  | zero => simp
  | succ e =>
    have hq : IsPrimePow (p ^ (e + 1)) :=
      (isPrimePow_nat_iff _).mpr ⟨p, e + 1, hp, by omega, rfl⟩
    have hqn := (isPrimePow_dvd_lcmPrefix_iff hq).mp hpe
    by_contra hd
    obtain ⟨a, ha, hlo, hhi⟩ := (isPrimePow_not_dvd_lcmInterval_iff hq hqn).mp hd
    have hg := mem_lcmIntervalGap.mpr ⟨hqn, hlo, hhi⟩
    have hw := lcmIntervalGap_width hg
    have hle : 2 * k ≤ (a + 1) * k := Nat.mul_le_mul_right k (by omega)
    omega

end DirichletL

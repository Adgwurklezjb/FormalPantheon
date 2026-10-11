import Arithmetic.LcmGrowth

/-!
Positive interval lcms for CDT v2 Section 2.2, supplied TeX 3291-3359.
The positive lower endpoint excludes zero when the width reaches n.
The exact von Mangoldt count retains all prime powers.
-/

namespace DirichletL

open scoped ArithmeticFunction.vonMangoldt

/-- The lcm of the positive integers between `n-k` and `n`, including endpoints. -/
def lcmInterval (n k : ℕ) : ℕ := (Finset.Icc (max 1 (n - k)) n).lcm id

theorem lcmInterval_zero (k : ℕ) : lcmInterval 0 k = 1 := by
  simp [lcmInterval]

theorem lcmInterval_self (n : ℕ) : lcmInterval n n = lcmPrefix n := by
  simp [lcmInterval, lcmPrefix]

theorem lcmInterval_zero_right {n : ℕ} (hn : 0 < n) : lcmInterval n 0 = n := by
  simp [lcmInterval, max_eq_right (show 1 ≤ n from hn)]

theorem lcmInterval_pos (n k : ℕ) : 0 < lcmInterval n k := by
  apply Nat.pos_of_ne_zero
  simp [lcmInterval, Finset.lcm_eq_zero_iff, max_le_iff]

theorem dvd_lcmInterval {n k m : ℕ} (hm : 1 ≤ m) (hlo : n - k ≤ m) (hhi : m ≤ n) :
    m ∣ lcmInterval n k := by
  exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨max_le hm hlo, hhi⟩)

theorem lcmInterval_dvd {n k l : ℕ} (hkl : k ≤ l) :
    lcmInterval n k ∣ lcmInterval n l := by
  apply Finset.lcm_mono
  intro m hm
  have hm' := Finset.mem_Icc.mp hm
  apply Finset.mem_Icc.mpr
  constructor
  · omega
  · exact hm'.2

theorem lcmInterval_dvd_lcmPrefix (n k : ℕ) : lcmInterval n k ∣ lcmPrefix n := by
  apply Finset.lcm_mono
  intro m hm
  have hm' := Finset.mem_Icc.mp hm
  exact Finset.mem_Icc.mpr ⟨(le_max_left 1 (n - k)).trans hm'.1, hm'.2⟩

theorem isPrimePow_dvd_lcmInterval_iff {q n k : ℕ} (hq : IsPrimePow q) :
    q ∣ lcmInterval n k ↔ ∃ a : ℕ, 0 < a ∧ n - k ≤ a * q ∧ a * q ≤ n := by
  rw [lcmInterval, isPrimePow_dvd_finset_lcm_iff hq]
  constructor
  · rintro ⟨m, hm, a, ha⟩
    have hm' := Finset.mem_Icc.mp hm
    have hm0 : 0 < m := (le_max_left 1 (n - k)).trans hm'.1
    have ha0 : 0 < a := by
      by_contra! h
      have hz : a = 0 := by omega
      simp only [hz, Nat.mul_zero] at ha
      omega
    have ham : a * q = m := (Nat.mul_comm a q).trans ha.symm
    refine ⟨a, ha0, ?_, ?_⟩
    · rw [ham]
      exact (le_max_right 1 (n - k)).trans hm'.1
    · rw [ham]
      exact hm'.2
  · rintro ⟨a, ha, hlo, hhi⟩
    refine ⟨a * q, Finset.mem_Icc.mpr ⟨max_le (mul_pos ha hq.pos) hlo, hhi⟩, ?_⟩
    exact ⟨a, Nat.mul_comm a q⟩

theorem isPrimePow_not_dvd_lcmInterval_iff {q n k : ℕ} (hq : IsPrimePow q)
    (hqn : q ≤ n) :
    ¬q ∣ lcmInterval n k ↔
      ∃ a : ℕ, 0 < a ∧ a * q < n - k ∧ n < (a + 1) * q := by
  constructor
  · intro h
    have ha : 0 < n / q := Nat.div_pos hqn hq.pos
    have hlo : n / q * q < n - k := by
      by_contra! hge
      exact h ((isPrimePow_dvd_lcmInterval_iff hq).mpr
        ⟨n / q, ha, hge, Nat.div_mul_le_self n q⟩)
    refine ⟨n / q, ha, hlo, ?_⟩
    simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ n hq.pos
  · rintro ⟨a, _, hlo, hhi⟩ hd
    obtain ⟨b, _, hb, hb'⟩ := (isPrimePow_dvd_lcmInterval_iff hq).mp hd
    have h₁ : q * a < b * q := by
      simpa only [Nat.mul_comm] using hlo.trans_le hb
    have h₂ : b * q < q * (a + 1) := by
      simpa only [Nat.mul_comm] using hb'.trans_lt hhi
    exact Nat.not_dvd_of_between_consec_multiples h₁ h₂ ⟨b, Nat.mul_comm b q⟩

theorem log_lcmInterval_eq_sum_vonMangoldt (n k : ℕ) :
    Real.log (lcmInterval n k : ℝ) =
      ∑ q ∈ (Finset.range (n + 1)).filter (fun q => q ∣ lcmInterval n k), Λ q := by
  classical
  let S := (Finset.range (n + 1)).filter (fun q => q ∣ lcmInterval n k)
  have he : (lcmInterval n k).divisors.filter (fun q => Λ q ≠ 0) =
      S.filter (fun q => Λ q ≠ 0) := by
    ext q
    simp only [S, Finset.mem_filter, ArithmeticFunction.vonMangoldt_ne_zero_iff,
      Nat.mem_divisors, Finset.mem_range]
    constructor
    · rintro ⟨⟨hd, _⟩, hq⟩
      have hqn := (isPrimePow_dvd_lcmPrefix_iff hq).mp
        (hd.trans (lcmInterval_dvd_lcmPrefix n k))
      exact ⟨⟨Nat.lt_succ_iff.mpr hqn, hd⟩, hq⟩
    · rintro ⟨⟨_, hd⟩, hq⟩
      exact ⟨⟨hd, (lcmInterval_pos n k).ne'⟩, hq⟩
  calc
    Real.log (lcmInterval n k : ℝ) = ∑ q ∈ (lcmInterval n k).divisors, Λ q :=
      ArithmeticFunction.vonMangoldt_sum.symm
    _ = ∑ q ∈ (lcmInterval n k).divisors.filter (fun q => Λ q ≠ 0), Λ q :=
      (Finset.sum_filter_ne_zero _).symm
    _ = ∑ q ∈ S.filter (fun q => Λ q ≠ 0), Λ q := by rw [he]
    _ = ∑ q ∈ S, Λ q := Finset.sum_filter_ne_zero _

theorem log_lcmInterval_add_sum_vonMangoldt (n k : ℕ) :
    Real.log (lcmInterval n k : ℝ) +
      (∑ q ∈ (Finset.range (n + 1)).filter (fun q => ¬q ∣ lcmInterval n k), Λ q) =
        ∑ q ∈ Finset.range (n + 1), Λ q := by
  rw [log_lcmInterval_eq_sum_vonMangoldt]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

end DirichletL

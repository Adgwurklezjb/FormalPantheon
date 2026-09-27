import Arithmetic.Denominators

/-!
The positive-prefix lcm from CDT v2, Section 2.2 and the uniform lcm
input at supplied TeX 3291-3310. Prime-power divisibility identifies
its logarithm with the canonical von Mangoldt sum. The elementary
primorial bound supplies only a coarse growth estimate; the sharp
prime-number-theorem asymptotic is a separate obligation.
-/

namespace DirichletL

open scoped ArithmeticFunction.vonMangoldt

theorem isPrimePow_dvd_nat_lcm_iff {q a b : ℕ} (hq : IsPrimePow q) :
    q ∣ Nat.lcm a b ↔ q ∣ a ∨ q ∣ b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  obtain ⟨p, k, hp, _, rfl⟩ := (isPrimePow_nat_iff q).mp hq
  rw [hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero ha hb),
    hp.pow_dvd_iff_le_factorization ha, hp.pow_dvd_iff_le_factorization hb,
    Nat.factorization_lcm ha hb, Finsupp.sup_apply]
  exact le_max_iff

theorem isPrimePow_dvd_finset_lcm_iff {q : ℕ} (hq : IsPrimePow q) (s : Finset ℕ) :
    q ∣ s.lcm id ↔ ∃ n ∈ s, q ∣ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hq.ne_one]
  | @insert a s ha ih =>
    rw [Finset.lcm_insert]
    change q ∣ Nat.lcm a (s.lcm id) ↔ ∃ n ∈ insert a s, q ∣ n
    rw [isPrimePow_dvd_nat_lcm_iff hq, ih]
    simp

theorem isPrimePow_dvd_lcmPrefix_iff {q n : ℕ} (hq : IsPrimePow q) :
    q ∣ lcmPrefix n ↔ q ≤ n := by
  constructor
  · intro h
    obtain ⟨m, hm, hqm⟩ := (isPrimePow_dvd_finset_lcm_iff hq (Finset.Icc 1 n)).mp h
    exact (Nat.le_of_dvd (Finset.mem_Icc.mp hm).1 hqm).trans (Finset.mem_Icc.mp hm).2
  · exact fun h => dvd_lcmPrefix hq.pos h

theorem log_lcmPrefix_eq_sum_vonMangoldt (n : ℕ) :
    Real.log (lcmPrefix n : ℝ) = ∑ i ∈ Finset.range (n + 1), Λ i := by
  classical
  have he : (lcmPrefix n).divisors.filter (fun i => Λ i ≠ 0) =
      (Finset.range (n + 1)).filter (fun i => Λ i ≠ 0) := by
    ext i
    simp only [Finset.mem_filter, ArithmeticFunction.vonMangoldt_ne_zero_iff,
      Nat.mem_divisors, Finset.mem_range]
    constructor
    · rintro ⟨⟨hi, _⟩, hq⟩
      exact ⟨Nat.lt_succ_iff.mpr ((isPrimePow_dvd_lcmPrefix_iff hq).mp hi), hq⟩
    · rintro ⟨hi, hq⟩
      exact ⟨⟨(isPrimePow_dvd_lcmPrefix_iff hq).mpr (Nat.lt_succ_iff.mp hi),
        (lcmPrefix_pos n).ne'⟩, hq⟩
  calc
    Real.log (lcmPrefix n : ℝ) = ∑ i ∈ (lcmPrefix n).divisors, Λ i :=
      ArithmeticFunction.vonMangoldt_sum.symm
    _ = ∑ i ∈ (lcmPrefix n).divisors.filter (fun i => Λ i ≠ 0), Λ i :=
      (Finset.sum_filter_ne_zero _).symm
    _ = ∑ i ∈ (Finset.range (n + 1)).filter (fun i => Λ i ≠ 0), Λ i := by rw [he]
    _ = ∑ i ∈ Finset.range (n + 1), Λ i := Finset.sum_filter_ne_zero _

theorem lcmPrefix_dvd_primorial_mul_half (n : ℕ) :
    lcmPrefix n ∣ primorial n * lcmPrefix (n / 2) := by
  apply Finset.lcm_dvd
  intro m hm
  have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
  have hmn : m ≤ n := (Finset.mem_Icc.mp hm).2
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k hp hpk
  cases k with
  | zero => simp
  | succ k =>
    have hpn : p ≤ n :=
      (Nat.le_of_dvd hm0 ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hpk)).trans hmn
    have hpprim : p ∣ primorial n := by
      apply Finset.dvd_prod_of_mem
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hpn), hp⟩
    have hpow : p ^ k * p ≤ n := by
      simpa only [pow_succ] using (Nat.le_of_dvd hm0 hpk).trans hmn
    have hhalf : p ^ k ≤ n / 2 :=
      (Nat.le_div_iff_mul_le (by decide)).mpr ((Nat.mul_le_mul_left (p ^ k) hp.two_le).trans hpow)
    have hsmall := dvd_lcmPrefix (pow_pos hp.pos k) hhalf
    simpa only [pow_succ'] using Nat.mul_dvd_mul hpprim hsmall

theorem lcmPrefix_le_four_pow_two_mul (n : ℕ) : lcmPrefix n ≤ 4 ^ (2 * n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · simp [hn, lcmPrefix_zero]
    have hhalf : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
    calc
      lcmPrefix n ≤ primorial n * lcmPrefix (n / 2) :=
        Nat.le_of_dvd (Nat.mul_pos (primorial_pos n) (lcmPrefix_pos _))
          (lcmPrefix_dvd_primorial_mul_half n)
      _ ≤ 4 ^ n * 4 ^ (2 * (n / 2)) :=
        Nat.mul_le_mul (primorial_le_4_pow n) (ih _ hhalf)
      _ = 4 ^ (n + 2 * (n / 2)) := (pow_add _ _ _).symm
      _ ≤ 4 ^ (2 * n) := Nat.pow_le_pow_right (by decide) (by omega)

theorem log_lcmPrefix_le (n : ℕ) :
    Real.log (lcmPrefix n : ℝ) ≤ (2 * Real.log 4) * (n : ℝ) := by
  have h := Real.log_le_log (show (0 : ℝ) < lcmPrefix n by exact_mod_cast lcmPrefix_pos n)
    (show (lcmPrefix n : ℝ) ≤ 4 ^ (2 * n) by exact_mod_cast lcmPrefix_le_four_pow_two_mul n)
  rw [Real.log_pow] at h
  push_cast at h
  nlinarith

theorem sum_vonMangoldt_le (n : ℕ) :
    (∑ i ∈ Finset.range n, Λ i) ≤ (2 * Real.log 4) * (n : ℝ) := by
  calc
    (∑ i ∈ Finset.range n, Λ i) ≤ ∑ i ∈ Finset.range (n + 1), Λ i := by
      rw [Finset.sum_range_succ]
      exact le_add_of_nonneg_right ArithmeticFunction.vonMangoldt_nonneg
    _ = Real.log (lcmPrefix n : ℝ) := (log_lcmPrefix_eq_sum_vonMangoldt n).symm
    _ ≤ _ := log_lcmPrefix_le n

end DirichletL

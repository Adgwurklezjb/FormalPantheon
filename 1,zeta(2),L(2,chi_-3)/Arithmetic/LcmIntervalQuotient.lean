import Arithmetic.LcmInterval

/-!
The exact cutoff quotient in CDT v2 Section 2.2 and the denominator
preview at supplied TeX 4260-4283. The cutoff removes the common
prime-power valuations with the positive-prefix lcm.
-/

namespace DirichletL

/-- The interval-lcm factor left after the prefix at the cutoff is available. -/
def lcmIntervalQuotient (n k c : ℕ) : ℕ :=
  lcmInterval n k / Nat.gcd (lcmInterval n k) (lcmPrefix c)

theorem lcmIntervalQuotient_pos (n k c : ℕ) : 0 < lcmIntervalQuotient n k c :=
  Nat.div_gcd_pos_of_pos_left _ (lcmInterval_pos n k)

theorem lcmIntervalQuotient_zero_cutoff (n k : ℕ) :
    lcmIntervalQuotient n k 0 = lcmInterval n k := by
  simp [lcmIntervalQuotient, lcmPrefix_zero]

theorem lcmIntervalQuotient_dvd (n k c : ℕ) :
    lcmIntervalQuotient n k c ∣ lcmInterval n k :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)

theorem lcmIntervalQuotient_dvd_iff {n k c r : ℕ} :
    lcmIntervalQuotient n k c ∣ r ↔ lcmInterval n k ∣ lcmPrefix c * r := by
  rw [lcmIntervalQuotient, Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left _ _)
    (Nat.gcd_pos_of_pos_left _ (lcmInterval_pos n k)), Nat.dvd_gcd_mul_iff_dvd_mul]

theorem lcmInterval_dvd_prefix_mul_quotient (n k c : ℕ) :
    lcmInterval n k ∣ lcmPrefix c * lcmIntervalQuotient n k c :=
  lcmIntervalQuotient_dvd_iff.mp dvd_rfl

theorem lcmIntervalQuotient_dvd_of_width_le {n k l c : ℕ} (hkl : k ≤ l) :
    lcmIntervalQuotient n k c ∣ lcmIntervalQuotient n l c :=
  lcmIntervalQuotient_dvd_iff.mpr
    ((lcmInterval_dvd hkl).trans (lcmInterval_dvd_prefix_mul_quotient n l c))

theorem lcmIntervalQuotient_dvd_of_cutoff_le {n k c d : ℕ} (hcd : c ≤ d) :
    lcmIntervalQuotient n k d ∣ lcmIntervalQuotient n k c :=
  lcmIntervalQuotient_dvd_iff.mpr
    ((lcmInterval_dvd_prefix_mul_quotient n k c).trans
      (Nat.mul_dvd_mul (lcmPrefix_dvd hcd) dvd_rfl))

theorem lcmIntervalQuotient_eq_one_of_le_cutoff {n k c : ℕ} (hnc : n ≤ c) :
    lcmIntervalQuotient n k c = 1 := by
  apply Nat.dvd_one.mp
  rw [lcmIntervalQuotient_dvd_iff, mul_one]
  exact (lcmInterval_dvd_lcmPrefix n k).trans (lcmPrefix_dvd hnc)

theorem lcmIntervalQuotient_dvd_prefix_div {n k c : ℕ} (hcn : c ≤ n) :
    lcmIntervalQuotient n k c ∣ lcmPrefix n / lcmPrefix c := by
  rw [lcmIntervalQuotient_dvd_iff, Nat.mul_div_cancel' (lcmPrefix_dvd hcn)]
  exact lcmInterval_dvd_lcmPrefix n k

theorem log_lcmIntervalQuotient_le_log_lcmInterval (n k c : ℕ) :
    Real.log (lcmIntervalQuotient n k c : ℝ) ≤ Real.log (lcmInterval n k : ℝ) := by
  apply Real.log_le_log (by exact_mod_cast lcmIntervalQuotient_pos n k c)
  exact_mod_cast Nat.le_of_dvd (lcmInterval_pos n k) (lcmIntervalQuotient_dvd n k c)

theorem log_lcmIntervalQuotient_le_log_prefix_sub {n k c : ℕ} (hcn : c ≤ n) :
    Real.log (lcmIntervalQuotient n k c : ℝ) ≤
      Real.log (lcmPrefix n : ℝ) - Real.log (lcmPrefix c : ℝ) := by
  have hp : 0 < lcmPrefix n / lcmPrefix c :=
    Nat.div_pos (Nat.le_of_dvd (lcmPrefix_pos n) (lcmPrefix_dvd hcn)) (lcmPrefix_pos c)
  have hN : (lcmPrefix n : ℝ) ≠ 0 := by exact_mod_cast (lcmPrefix_pos n).ne'
  have hC : (lcmPrefix c : ℝ) ≠ 0 := by exact_mod_cast (lcmPrefix_pos c).ne'
  calc
    _ ≤ Real.log ((lcmPrefix n / lcmPrefix c : ℕ) : ℝ) := by
      apply Real.log_le_log (by exact_mod_cast lcmIntervalQuotient_pos n k c)
      exact_mod_cast Nat.le_of_dvd hp (lcmIntervalQuotient_dvd_prefix_div (k := k) hcn)
    _ = _ := by rw [Nat.cast_div_charZero (lcmPrefix_dvd hcn), Real.log_div hN hC]

end DirichletL

import Mathlib

/-!
The selected integral sequence C from Zagier (2009), sequence C and Equation
(3), as used in CDT v2 Section 11.1. The finite formula is proved directly;
the summand-level telescoping certificate is recorded below.
-/

namespace DirichletL

/-- Zagier's sequence C: `sum k, choose n k ^ 2 * choose (2*k) k`. -/
def zagierC (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.choose n k ^ 2 * Nat.choose (2 * k) k

/-- The rational summand used when applying the telescoping certificate. -/
def zagierSummand (n k : ℕ) : ℚ :=
  (Nat.choose n k : ℚ) ^ 2 * (Nat.choose (2 * k) k : ℚ)

/-- Certificate term for the summand recurrence, with `n` fixed. -/
def zagierCertificate (n k : ℕ) : ℚ :=
  (k : ℚ) ^ 3 * (3 * (k : ℚ) - 4 * ((n + 1 : ℕ) : ℚ)) * zagierSummand (n + 1) k

set_option maxHeartbeats 800000 in
theorem zagier_certificate_identity {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    ((n + 1 : ℚ) ^ 2 * zagierSummand (n + 1) k -
      (10 * (n : ℚ) * (n + 1 : ℚ) + 3) * zagierSummand n k +
      9 * (n : ℚ) ^ 2 * zagierSummand (n - 1) k) * (n + 1 : ℚ) ^ 2 =
      zagierCertificate n (k + 1) - zagierCertificate n k := by
  have hn0 : (n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
  have hk1 : (k + 1 : ℚ) ≠ 0 := by positivity
  have hm : k ≤ n + 1 := Nat.le_trans hk (Nat.le_succ n)
  have hmcast : ((n + 1 - k : ℕ) : ℚ) = (n + 1 : ℚ) - k := by
    rw [Nat.cast_sub hm]
    norm_num
  have htopNat := Nat.choose_succ_right_eq (n + 1) k
  have htop2Nat := Nat.choose_mul_succ_eq n k
  have htop2 : (Nat.choose n k : ℚ) * (n + 1) =
      (Nat.choose (n + 1) k : ℚ) * ((n + 1 : ℚ) - k) := by
    have h := congrArg (fun z : ℕ => (z : ℚ)) htop2Nat
    simpa [Nat.cast_sub hm] using h
  have htop0 : ((n + 1 : ℚ) - k) ≠ 0 := by
    rw [← hmcast]
    exact_mod_cast (Nat.ne_of_gt (show 0 < n + 1 - k by omega))
  have htop2' : (Nat.choose (n + 1) k : ℚ) =
      (Nat.choose n k : ℚ) * (n + 1) / ((n + 1 : ℚ) - k) := by
    apply (eq_div_iff htop0).2
    nlinarith [htop2]
  have htop : (Nat.choose (n + 1) (k + 1) : ℚ) * (k + 1) =
      (Nat.choose (n + 1) k : ℚ) * ((n + 1 : ℚ) - k) := by
    have h := congrArg (fun z : ℕ => (z : ℚ)) htopNat
    simpa [Nat.cast_sub hm] using h
  have hprevNat := Nat.choose_mul_succ_eq (n - 1) k
  have hnsub : n - 1 + 1 = n := by omega
  rw [hnsub] at hprevNat
  have hprev : (Nat.choose (n - 1) k : ℚ) * n =
      (Nat.choose n k : ℚ) * ((n : ℚ) - k) := by
    have h := congrArg (fun z : ℕ => (z : ℚ)) hprevNat
    simpa [Nat.cast_sub hk] using h
  have hc1Nat := Nat.choose_mul_succ_eq (2 * k) k
  have hc2Nat := Nat.choose_mul_succ_eq (2 * k + 1) (k + 1)
  have hc1 : (Nat.choose (2 * k) k : ℚ) * (2 * k + 1) =
      (Nat.choose (2 * k + 1) k : ℚ) * (k + 1) := by
    have hsub : 2 * k + 1 - k = k + 1 := by omega
    rw [hsub] at hc1Nat
    have h := congrArg (fun z : ℕ => (z : ℚ)) hc1Nat
    simpa using h
  have hc2 : (Nat.choose (2 * k + 1) (k + 1) : ℚ) * (2 * k + 2) =
      (Nat.choose (2 * k + 2) (k + 1) : ℚ) * (k + 1) := by
    have hsub : 2 * k + 1 + 1 - (k + 1) = k + 1 := by omega
    have hidx : 2 * k + 1 + 1 = 2 * k + 2 := by omega
    rw [hsub, hidx] at hc2Nat
    have h := congrArg (fun z : ℕ => (z : ℚ)) hc2Nat
    simpa using h
  have hsymmNat : (2 * k + 1).choose (k + 1) = (2 * k + 1).choose k := by
    have h := Nat.choose_symm_add (a := k) (b := k + 1)
    simpa [show k + (k + 1) = 2 * k + 1 by omega] using h.symm
  have hsymm : (Nat.choose (2 * k + 1) (k + 1) : ℚ) =
      (Nat.choose (2 * k + 1) k : ℚ) := by exact_mod_cast hsymmNat
  have hc : (Nat.choose (2 * k + 2) (k + 1) : ℚ) * (k + 1) ^ 2 =
      (Nat.choose (2 * k) k : ℚ) * (2 * k + 1) * (2 * k + 2) := by
    calc
      _ = ((Nat.choose (2 * k + 2) (k + 1) : ℚ) * (k + 1)) * (k + 1) := by ring
      _ = ((Nat.choose (2 * k + 1) (k + 1) : ℚ) * (2 * k + 2)) * (k + 1) := by
        rw [hc2]
      _ = ((Nat.choose (2 * k + 1) k : ℚ) * (k + 1)) * (2 * k + 2) := by
        rw [hsymm]
        ring
      _ = ((Nat.choose (2 * k) k : ℚ) * (2 * k + 1)) * (2 * k + 2) := by
        rw [← hc1]
      _ = _ := by ring
  have htop' : (Nat.choose (n + 1) (k + 1) : ℚ) =
      (Nat.choose (n + 1) k : ℚ) * ((n + 1 : ℚ) - k) / (k + 1) :=
    (eq_div_iff hk1).2 htop
  have hprev' : (Nat.choose (n - 1) k : ℚ) =
      (Nat.choose n k : ℚ) * ((n : ℚ) - k) / n :=
    (eq_div_iff hn0).2 hprev
  have hc' : (Nat.choose (2 * k + 2) (k + 1) : ℚ) =
      (Nat.choose (2 * k) k : ℚ) * (2 * k + 1) * (2 * k + 2) / (k + 1) ^ 2 :=
    (eq_div_iff (pow_ne_zero 2 hk1)).2 hc
  simp only [zagierSummand, zagierCertificate]
  have htwo : 2 * (k + 1) = 2 * k + 2 := by omega
  rw [htwo]
  simp [htop2', htop', hprev', hc']
  field_simp
  ring

theorem zagier_certificate_sum (n r : ℕ) :
    ∑ k ∈ Finset.range r, (zagierCertificate n (k + 1) - zagierCertificate n k) =
      zagierCertificate n r - zagierCertificate n 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem zagier_certificate_zero (n : ℕ) : zagierCertificate n 0 = 0 := by
  simp [zagierCertificate]

theorem zagier_certificate_boundary (n : ℕ) :
    zagierCertificate n (n + 1) =
      -((n + 1 : ℚ) ^ 4) * (Nat.choose (2 * (n + 1)) (n + 1) : ℚ) := by
  simp [zagierCertificate, zagierSummand]
  ring

set_option maxHeartbeats 800000 in
theorem zagierC_recurrence_rational {n : ℕ} (hn : 1 ≤ n) :
    (n + 1 : ℚ) ^ 2 * (zagierC (n + 1) : ℚ) -
        10 * (n : ℚ) * (n + 1 : ℚ) * (zagierC n : ℚ) +
        9 * (n : ℚ) ^ 2 * (zagierC (n - 1) : ℚ) =
      3 * (zagierC n : ℚ) := by
  let H : ℕ → ℚ := fun k =>
    (n + 1 : ℚ) ^ 2 * zagierSummand (n + 1) k -
      (10 * (n : ℚ) * (n + 1 : ℚ) + 3) * zagierSummand n k +
      9 * (n : ℚ) ^ 2 * zagierSummand (n - 1) k
  have hcast (r : ℕ) :
      ∑ k ∈ Finset.range (r + 1), zagierSummand r k = (zagierC r : ℚ) := by
    simp only [zagierSummand, zagierC]
    norm_cast
  have hsum_m :
      ∑ k ∈ Finset.range (n + 1), zagierSummand (n + 1) k =
        (zagierC (n + 1) : ℚ) -
          (Nat.choose (2 * (n + 1)) (n + 1) : ℚ) := by
    have hlast : zagierSummand (n + 1) (n + 1) =
        (Nat.choose (2 * (n + 1)) (n + 1) : ℚ) := by
      simp [zagierSummand]
    have hm := hcast (n + 1)
    rw [Finset.sum_range_succ, hlast] at hm
    linarith
  have hsum_n :
      ∑ k ∈ Finset.range (n + 1), zagierSummand n k = (zagierC n : ℚ) := by
    simpa using hcast n
  have hsum_prev :
      ∑ k ∈ Finset.range (n + 1), zagierSummand (n - 1) k =
        (zagierC (n - 1) : ℚ) := by
    rw [Finset.sum_range_succ]
    have hlast : zagierSummand (n - 1) n = 0 := by
      have hzero : Nat.choose (n - 1) n = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [zagierSummand, hzero]
    rw [hlast]
    simpa [Nat.sub_add_cancel (show 1 ≤ n by omega)] using hcast (n - 1)
  have hmul :
      (n + 1 : ℚ) ^ 2 * (∑ k ∈ Finset.range (n + 1), H k) =
        zagierCertificate n (n + 1) - zagierCertificate n 0 := by
    calc
      _ = ∑ k ∈ Finset.range (n + 1), ((n + 1 : ℚ) ^ 2 * H k) := by
        rw [Finset.mul_sum]
      _ = ∑ k ∈ Finset.range (n + 1),
          (zagierCertificate n (k + 1) - zagierCertificate n k) := by
        apply Finset.sum_congr rfl
        intro k hk
        simpa [H, mul_comm] using
          zagier_certificate_identity hn (Nat.le_of_lt_succ (Finset.mem_range.1 hk))
      _ = _ := zagier_certificate_sum n (n + 1)
  have hsum :
      ∑ k ∈ Finset.range (n + 1), H k =
        -(n + 1 : ℚ) ^ 2 * (Nat.choose (2 * (n + 1)) (n + 1) : ℚ) := by
    apply (mul_left_cancel₀ (show (n + 1 : ℚ) ^ 2 ≠ 0 by positivity))
    rw [hmul, zagier_certificate_boundary, zagier_certificate_zero]
    ring
  have hsum_expand :
      ∑ k ∈ Finset.range (n + 1), H k =
        (n + 1 : ℚ) ^ 2 * ∑ k ∈ Finset.range (n + 1), zagierSummand (n + 1) k -
          (10 * (n : ℚ) * (n + 1 : ℚ) + 3) *
            ∑ k ∈ Finset.range (n + 1), zagierSummand n k +
          9 * (n : ℚ) ^ 2 *
            ∑ k ∈ Finset.range (n + 1), zagierSummand (n - 1) k := by
    simp only [H, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp_rw [← Finset.mul_sum]
  rw [hsum_expand, hsum_m, hsum_n, hsum_prev] at hsum
  nlinarith

theorem zagierC_recurrence {n : ℕ} (hn : 1 ≤ n) :
    ((n + 1 : ℤ) ^ 2 * (zagierC (n + 1) : ℤ) -
      10 * (n : ℤ) * (n + 1 : ℤ) * (zagierC n : ℤ) +
      9 * (n : ℤ) ^ 2 * (zagierC (n - 1) : ℤ)) =
      3 * (zagierC n : ℤ) := by
  have h := zagierC_recurrence_rational hn
  exact_mod_cast h

theorem zagierC_zero : zagierC 0 = 1 := by
  norm_num [zagierC]

theorem zagierC_one : zagierC 1 = 3 := by
  norm_num [zagierC, Finset.sum_range_succ, Nat.choose]

theorem zagierC_two : zagierC 2 = 15 := by
  norm_num [zagierC, Finset.sum_range_succ, Nat.choose]

theorem zagierC_three : zagierC 3 = 93 := by
  norm_num [zagierC, Finset.sum_range_succ, Nat.choose]

theorem zagierC_four : zagierC 4 = 639 := by
  norm_num [zagierC, Finset.sum_range_succ, Nat.choose]

theorem zagierC_integral (n : ℕ) : ∃ z : ℤ, (zagierC n : ℤ) = z := by
  exact ⟨zagierC n, rfl⟩

/-- Zagier's recurrence (3), with the predecessor interpreted by `Nat.pred`. -/
def zagierCRecurrenceAt (n : ℕ) : Prop :=
  1 ≤ n →
    ((n + 1 : ℤ) ^ 2 * (zagierC (n + 1) : ℤ) -
      10 * (n : ℤ) * (n + 1 : ℤ) * (zagierC n : ℤ) +
      9 * (n : ℤ) ^ 2 * (zagierC (n - 1) : ℤ)) =
      3 * (zagierC n : ℤ)

theorem zagierC_recurrence_one : zagierCRecurrenceAt 1 := by
  norm_num [zagierCRecurrenceAt, zagierC, Finset.sum_range_succ, Nat.choose]

theorem zagierC_recurrence_two : zagierCRecurrenceAt 2 := by
  norm_num [zagierCRecurrenceAt, zagierC, Finset.sum_range_succ, Nat.choose]

theorem zagierC_recurrence_three : zagierCRecurrenceAt 3 := by
  norm_num [zagierCRecurrenceAt, zagierC, Finset.sum_range_succ, Nat.choose]

end DirichletL

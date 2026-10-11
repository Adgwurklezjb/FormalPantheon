import Mathlib

/-!
Finite q-binomial identities for the theta/product bridge in CDT v2 Section
11.1. See Lau-Lee-Ono v3, Sections 3.2 and 3.4.1, and the boundary correction
-/

namespace DirichletL

section Semiring

variable {R : Type*} [CommSemiring R]

/-- The Gaussian binomial coefficient, with zero outside the finite triangle. -/
def qBinomial (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinomial q n k + q ^ (k + 1) * qBinomial q n (k + 1)

@[simp] theorem qBinomial_zero_right (q : R) (n : ℕ) : qBinomial q n 0 = 1 := by
  cases n <;> rfl

@[simp] theorem qBinomial_zero_succ (q : R) (k : ℕ) : qBinomial q 0 (k + 1) = 0 := rfl

theorem qBinomial_succ_succ (q : R) (n k : ℕ) :
    qBinomial q (n + 1) (k + 1) =
      qBinomial q n k + q ^ (k + 1) * qBinomial q n (k + 1) := rfl

theorem qBinomial_eq_zero_of_lt (q : R) {n k : ℕ} (hnk : n < k) :
    qBinomial q n k = 0 := by
  induction n generalizing k with
  | zero => cases k <;> simp_all
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k =>
      rw [qBinomial_succ_succ, ih (by omega), ih (by omega)]
      simp

@[simp] theorem qBinomial_self (q : R) (n : ℕ) : qBinomial q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [qBinomial_succ_succ, ih, qBinomial_eq_zero_of_lt q (Nat.lt_succ_self n)]
    simp

theorem qBinomial_one (n k : ℕ) : qBinomial (1 : R) n k = (n.choose k : R) := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => simp [qBinomial_succ_succ, ih, Nat.choose_succ_succ]

end Semiring

theorem le_choose_two_add_one (k : ℕ) : k ≤ k.choose 2 + 1 := by
  cases k with
  | zero => simp
  | succ k =>
    have h : (k + 1).choose 2 = k + k.choose 2 := by
      simpa using Nat.choose_succ_succ k 1
    rw [h]
    omega

section Ring

variable {R : Type*} [CommRing R]

/-- The finite q-Pochhammer product, with first factor `1 - a`. -/
def qPochhammer (a q : R) (n : ℕ) : R :=
  ∏ i ∈ Finset.range n, (1 - a * q ^ i)

@[simp] theorem qPochhammer_zero (a q : R) : qPochhammer a q 0 = 1 := by
  simp [qPochhammer]

theorem qPochhammer_succ (a q : R) (n : ℕ) :
    qPochhammer a q (n + 1) = qPochhammer a q n * (1 - a * q ^ n) := by
  exact Finset.prod_range_succ _ _

theorem qPochhammer_succ_left (a q : R) (n : ℕ) :
    qPochhammer a q (n + 1) = qPochhammer (a * q) q n * (1 - a) := by
  simp only [qPochhammer, Finset.prod_range_succ', pow_succ', ← mul_assoc, pow_zero,
    mul_one]

theorem qPochhammer_add (a q : R) (m n : ℕ) :
    qPochhammer a q (m + n) =
      qPochhammer a q m * qPochhammer (a * q ^ m) q n := by
  simp only [qPochhammer, Finset.prod_range_add, pow_add, ← mul_assoc]

theorem qPochhammer_self_succ (q : R) (n : ℕ) :
    qPochhammer q q (n + 1) = qPochhammer q q n * (1 - q ^ (n + 1)) := by
  simpa only [pow_succ'] using qPochhammer_succ q q n

theorem dvd_qPochhammer_sub_one {d a q : R} (ha : d ∣ a) (n : ℕ) :
    d ∣ qPochhammer a q n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qPochhammer_succ]
    have heq : qPochhammer a q n * (1 - a * q ^ n) - 1 =
        (qPochhammer a q n - 1) - (qPochhammer a q n * a) * q ^ n := by ring
    rw [heq]
    exact dvd_sub ih (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ha _) _)

theorem qBinomial_mul_qPochhammer (q : R) {n k : ℕ} (hk : k ≤ n) :
    qBinomial q n k * qPochhammer q q k * qPochhammer q q (n - k) =
      qPochhammer q q n := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst k
    simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      by_cases hkn : k = n
      · subst k
        simp
      have hkn' : k + 1 ≤ n := by omega
      have hsub : n + 1 - (k + 1) = n - k := by omega
      have hp : qPochhammer q q (n - k) =
          qPochhammer q q (n - (k + 1)) * (1 - q ^ (n - k)) := by
        have he : n - k = (n - (k + 1)) + 1 := by omega
        conv_lhs => rw [he, qPochhammer_self_succ]
        rw [← he]
      rw [qBinomial_succ_succ, hsub]
      calc
        _ = (qBinomial q n k * qPochhammer q q k * qPochhammer q q (n - k)) *
              (1 - q ^ (k + 1)) +
            q ^ (k + 1) * (qBinomial q n (k + 1) * qPochhammer q q (k + 1) *
              qPochhammer q q (n - (k + 1))) * (1 - q ^ (n - k)) := by
                rw [qPochhammer_self_succ, hp]
                ring
        _ = qPochhammer q q n * (1 - q ^ (k + 1)) +
            q ^ (k + 1) * qPochhammer q q n * (1 - q ^ (n - k)) := by
              rw [ih (by omega), ih hkn']
        _ = qPochhammer q q n * (1 - q ^ (n + 1)) := by
              have he : n + 1 = (k + 1) + (n - k) := by omega
              rw [he, pow_add]
              ring
        _ = qPochhammer q q (n + 1) := (qPochhammer_self_succ q n).symm

private theorem sum_qBinomial_succ (a q : R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2),
      qBinomial q (n + 1) k * (-a) ^ k * q ^ k.choose 2) =
      (∑ k ∈ Finset.range (n + 1),
        qBinomial q n k * (-(a * q)) ^ k * q ^ k.choose 2) * (1 - a) := by
  let f (k : ℕ) := qBinomial q n k * (-(a * q)) ^ k * q ^ k.choose 2
  have hf0 : f 0 = 1 := by simp [f]
  have hfn : f (n + 1) = 0 := by
    simp [f, qBinomial_eq_zero_of_lt q (Nat.lt_succ_self n)]
  have hs : (∑ k ∈ Finset.range (n + 1), f (k + 1)) + 1 =
      ∑ k ∈ Finset.range (n + 1), f k := by
    have h := Finset.sum_range_succ' f (n + 1)
    rw [Finset.sum_range_succ, hf0, hfn, add_zero] at h
    exact h.symm
  have ht (k : ℕ) : qBinomial q (n + 1) (k + 1) * (-a) ^ (k + 1) *
      q ^ (k + 1).choose 2 = f (k + 1) + (-a) * f k := by
    dsimp [f]
    rw [qBinomial_succ_succ]
    have hc : (k + 1).choose 2 = k + k.choose 2 := by
      simpa using Nat.choose_succ_succ k 1
    simp only [hc, pow_add, pow_succ, neg_mul, mul_pow]
    ring
  calc
    _ = (∑ k ∈ Finset.range (n + 1), (f (k + 1) + (-a) * f k)) + 1 := by
      rw [Finset.sum_range_succ']
      simp only [qBinomial_zero_right, pow_zero, Nat.choose_zero_succ, mul_one]
      congr 1
      exact Finset.sum_congr rfl fun k _ => ht k
    _ = ((∑ k ∈ Finset.range (n + 1), f (k + 1)) + 1) +
        (-a) * (∑ k ∈ Finset.range (n + 1), f k) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          ring
    _ = (∑ k ∈ Finset.range (n + 1), f k) * (1 - a) := by rw [hs]; ring

/-- The finite q-binomial theorem, valid even at roots of unity. -/
theorem qPochhammer_eq_sum_qBinomial (a q : R) (n : ℕ) :
    qPochhammer a q n = ∑ k ∈ Finset.range (n + 1),
      qBinomial q n k * (-a) ^ k * q ^ k.choose 2 := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [qPochhammer_succ_left, ih, sum_qBinomial_succ]

end Ring

end DirichletL

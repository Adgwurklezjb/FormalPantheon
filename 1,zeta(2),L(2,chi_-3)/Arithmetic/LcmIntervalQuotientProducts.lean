import Arithmetic.IntegerProducts
import Arithmetic.LcmIntervalQuotient

/-!
Exact cutoff clearing for products of coefficient denominators in CDT v2,
supplied TeX 4440-4518. The literal quotient retains all prime powers.
-/

namespace DirichletL

theorem max_one_dvd_lcmInterval {n k r : ℕ} (hlo : n - k ≤ r) (hhi : r ≤ n) :
    max 1 r ∣ lcmInterval n k := by
  by_cases hr : r = 0
  · simp [hr]
  · have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr
    rw [max_eq_right hr1]
    exact dvd_lcmInterval hr1 hlo hhi

theorem max_one_pow_dvd_prefix_mul_quotient {n k c r e E : ℕ}
    (hlo : n - k ≤ r) (hhi : r ≤ n) (he : e ≤ E) :
    (max 1 r) ^ e ∣ lcmPrefix c ^ e * lcmIntervalQuotient n k c ^ E := by
  have hd : max 1 r ∣ lcmPrefix c * lcmIntervalQuotient n k c :=
    (max_one_dvd_lcmInterval hlo hhi).trans (lcmInterval_dvd_prefix_mul_quotient n k c)
  have hp := pow_dvd_pow_of_dvd hd e
  rw [mul_pow] at hp
  exact hp.trans (Nat.mul_dvd_mul_left _ (pow_dvd_pow _ he))

theorem prod_max_one_pow_dvd_prefix_mul_quotient {ι : Type*} (s : Finset ι)
    (n r e : ι → ℕ) (k c E : ℕ) (hlo : ∀ i ∈ s, n i - k ≤ r i)
    (hhi : ∀ i ∈ s, r i ≤ n i) (he : ∀ i ∈ s, e i ≤ E) :
    (∏ i ∈ s, (max 1 (r i)) ^ e i) ∣
      lcmPrefix c ^ (∑ i ∈ s, e i) * ∏ i ∈ s, lcmIntervalQuotient (n i) k c ^ E := by
  have h := Finset.prod_dvd_prod_of_dvd
    (fun i => (max 1 (r i)) ^ e i)
    (fun i => lcmPrefix c ^ e i * lcmIntervalQuotient (n i) k c ^ E)
    (fun i hi => max_one_pow_dvd_prefix_mul_quotient (hlo i hi) (hhi i hi) (he i hi))
  simpa only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] using h

theorem isInteger_prefix_mul_quotient_prod {ι : Type*} (s : Finset ι)
    (n r e : ι → ℕ) (q : ι → ℚ) (k c E : ℕ)
    (hlo : ∀ i ∈ s, n i - k ≤ r i) (hhi : ∀ i ∈ s, r i ≤ n i)
    (he : ∀ i ∈ s, e i ≤ E)
    (hzero : ∀ i ∈ s, r i = 0 → IsLocalization.IsInteger ℤ (q i))
    (hcoeff : ∀ i ∈ s, IsLocalization.IsInteger ℤ ((r i : ℚ) ^ e i * q i)) :
    IsLocalization.IsInteger ℤ
      (((lcmPrefix c ^ (∑ i ∈ s, e i) * ∏ i ∈ s, lcmIntervalQuotient (n i) k c ^ E : ℕ) : ℚ) *
        ∏ i ∈ s, q i) := by
  have h := isInteger_nat_mul_prod s (fun i => (max 1 (r i)) ^ e i) q
    (fun i hi => isInteger_max_one_pow_mul (hzero i hi) (hcoeff i hi))
  exact isInteger_nat_mul_of_dvd h
    (prod_max_one_pow_dvd_prefix_mul_quotient s n r e k c E hlo hhi he)

theorem log_prefix_mul_quotient_prod {ι : Type*} (s : Finset ι)
    (n e : ι → ℕ) (k c E : ℕ) :
    Real.log ((lcmPrefix c ^ (∑ i ∈ s, e i) *
      ∏ i ∈ s, lcmIntervalQuotient (n i) k c ^ E : ℕ) : ℝ) =
        ((∑ i ∈ s, e i : ℕ) : ℝ) * Real.log (lcmPrefix c : ℝ) +
          ∑ i ∈ s, (E : ℝ) * Real.log (lcmIntervalQuotient (n i) k c : ℝ) := by
  have hP : ((lcmPrefix c ^ (∑ i ∈ s, e i) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (pow_pos (lcmPrefix_pos c) (∑ i ∈ s, e i)).ne'
  have hQ : ((∏ i ∈ s, lcmIntervalQuotient (n i) k c ^ E : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.prod_pos (fun i _ => pow_pos (lcmIntervalQuotient_pos (n i) k c) E)).ne'
  rw [Nat.cast_mul, Real.log_mul hP hQ, Nat.cast_pow, Real.log_pow, Nat.cast_prod,
    Real.log_prod _ _ (fun i _ => by
      exact_mod_cast (pow_pos (lcmIntervalQuotient_pos (n i) k c) E).ne')]
  simp only [Nat.cast_pow, Real.log_pow]

end DirichletL

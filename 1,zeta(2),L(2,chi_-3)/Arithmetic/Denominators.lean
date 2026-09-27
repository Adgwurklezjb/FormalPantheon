import Foundations.ChiMinusThree

/-!
The first arithmetic layer for the positive-prefix lcm used by CDT v2,
Section 2.2. Sequence-specific denominator transfer is intentionally separate.
-/

namespace DirichletL

/-- Multiplication by `m^2` sends this rational value to an integer. -/
def SqIntegral (q : ℚ) (m : ℕ) : Prop :=
  ∃ z : ℤ, (m : ℚ) ^ 2 * q = z

theorem SqIntegral.zero (m : ℕ) : SqIntegral 0 m := by
  exact ⟨0, by simp⟩

theorem SqIntegral.add {q r : ℚ} {m : ℕ} (hq : SqIntegral q m)
    (hr : SqIntegral r m) : SqIntegral (q + r) m := by
  obtain ⟨z, hz⟩ := hq
  obtain ⟨w, hw⟩ := hr
  exact ⟨z + w, by rw [mul_add, hz, hw, Int.cast_add]⟩

theorem SqIntegral.mul_intCast {q : ℚ} {m : ℕ} (hq : SqIntegral q m) (z : ℤ) :
    SqIntegral (q * z) m := by
  obtain ⟨w, hw⟩ := hq
  exact ⟨w * z, by rw [← mul_assoc, hw, Int.cast_mul]⟩

theorem SqIntegral.of_dvd {q : ℚ} {m n : ℕ} (hq : SqIntegral q m) (hmn : m ∣ n) :
    SqIntegral q n := by
  obtain ⟨z, hz⟩ := hq
  obtain ⟨k, rfl⟩ := hmn
  refine ⟨(k : ℤ) ^ 2 * z, ?_⟩
  push_cast
  calc
    ((m : ℚ) * k) ^ 2 * q = (k : ℚ) ^ 2 * ((m : ℚ) ^ 2 * q) := by ring
    _ = (k : ℚ) ^ 2 * z := by rw [hz]

theorem SqIntegral.sum {ι : Type*} (s : Finset ι) {f : ι → ℚ} {m : ℕ}
    (h : ∀ i ∈ s, SqIntegral (f i) m) : SqIntegral (∑ i ∈ s, f i) m := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SqIntegral.zero m
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- The checked integer numerator from the q-coefficient formula in CDT v2. -/
def betaNumerator (m : ℕ) : ℤ :=
  ∑ d ∈ m.divisors,
    (-1 : ℤ) ^ (d - 1) * chiMinusThreeInt (m / d) * (d : ℤ) ^ 2

/-- The rational divisor-sum coefficient, defined only as arithmetic data here. -/
def betaCoeff (m : ℕ) : ℚ :=
  (betaNumerator m : ℚ) / (m : ℚ) ^ 2

/-- The constant coefficient in the arithmetic beta convention vanishes. -/
theorem betaCoeff_zero : betaCoeff 0 = 0 := by
  simp [betaCoeff]

/--
The beta coefficient in the complementary divisor indexing used by the
q-series construction.  The hypothesis excludes the zero divisor set and
allows exact cancellation of the factor `m^2`.
-/
theorem betaCoeff_eq_divisorSum {m : ℕ} (hm : m ≠ 0) :
    betaCoeff m =
      ∑ n ∈ m.divisors,
        (chiMinusThreeInt n : ℚ) / (n : ℚ) ^ 2 *
          (-1 : ℚ) ^ (m / n - 1) := by
  let f : ℕ → ℚ := fun n =>
    (chiMinusThreeInt n : ℚ) * (-1 : ℚ) ^ (m / n - 1) * ((m / n : ℕ) : ℚ) ^ 2
  have hsum_cast :
      (betaNumerator m : ℚ) =
        ∑ d ∈ m.divisors,
          (-1 : ℚ) ^ (d - 1) * (chiMinusThreeInt (m / d) : ℚ) *
            (d : ℚ) ^ 2 := by
    simp [betaNumerator, Int.cast_sum, Int.cast_pow]
  have hterm_reindex (d : ℕ) (hd : d ∈ m.divisors) :
      ((-1 : ℚ) ^ (d - 1) * (chiMinusThreeInt (m / d) : ℚ) *
          (d : ℚ) ^ 2) = f (m / d) := by
    have hdiv : d ∣ m := Nat.dvd_of_mem_divisors hd
    have hdd : m / (m / d) = d := Nat.div_div_self hdiv hm
    simp [f, hdd, mul_comm, mul_left_comm, mul_assoc]
  have hterm_cancel (n : ℕ) (hn : n ∈ m.divisors) :
      f n / (m : ℚ) ^ 2 =
        (chiMinusThreeInt n : ℚ) / (n : ℚ) ^ 2 *
          (-1 : ℚ) ^ (m / n - 1) := by
    have hdiv : n ∣ m := Nat.dvd_of_mem_divisors hn
    have hnpos : 0 < n := Nat.pos_of_mem_divisors hn
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
    have hmq : (m : ℚ) = (n : ℚ) * ((m / n : ℕ) : ℚ) := by
      exact_mod_cast (Nat.mul_div_cancel' hdiv).symm
    have hquot : ((m / n : ℕ) : ℚ) ≠ 0 := by
      exact right_ne_zero_of_mul (hmq ▸ (show (m : ℚ) ≠ 0 by exact_mod_cast hm))
    simp only [f]
    rw [hmq]
    field_simp [hnq, hquot]
  unfold betaCoeff
  rw [hsum_cast]
  calc
    (∑ d ∈ m.divisors,
        (-1 : ℚ) ^ (d - 1) * (chiMinusThreeInt (m / d) : ℚ) *
          (d : ℚ) ^ 2) / (m : ℚ) ^ 2 =
        (∑ d ∈ m.divisors, f (m / d)) / (m : ℚ) ^ 2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro d hd
          exact hterm_reindex d hd
    _ = (∑ n ∈ m.divisors, f n) / (m : ℚ) ^ 2 := by
          rw [Nat.sum_div_divisors]
    _ = ∑ n ∈ m.divisors,
          (chiMinusThreeInt n : ℚ) / (n : ℚ) ^ 2 *
            (-1 : ℚ) ^ (m / n - 1) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro n hn
          exact hterm_cancel n hn

/-- The real-valued beta divisor formula from CDT v2, Section 11.1. -/
theorem betaCoeff_cast_eq_divisorSum {m : ℕ} (hm : m ≠ 0) :
    (betaCoeff m : ℝ) =
      ∑ n ∈ m.divisors,
        chiMinusThree n / (n : ℝ) ^ 2 * (-1 : ℝ) ^ (m / n - 1) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (betaCoeff_eq_divisorSum hm)
  simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_intCast, Rat.cast_natCast, Rat.cast_neg, Rat.cast_one,
    chiMinusThreeInt_cast] using h

/-- The companion checked integer numerator from the q-coefficient formula. -/
def gammaNumerator (m : ℕ) : ℤ :=
  (∑ d ∈ m.divisors, chiMinusThreeInt d * (d : ℤ) ^ 2) -
    if Even m then ∑ d ∈ (m / 2).divisors, chiMinusThreeInt d * (d : ℤ) ^ 2 else 0

/-- The companion rational divisor-sum coefficient. -/
def gammaCoeff (m : ℕ) : ℚ :=
  (gammaNumerator m : ℚ) / (m : ℚ) ^ 2

/-- The lcm of the positive integers in the prefix `[1, n]`. -/
def lcmPrefix (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

theorem lcmPrefix_zero : lcmPrefix 0 = 1 := by
  simp [lcmPrefix]

theorem dvd_lcmPrefix {n k : ℕ} (hk₁ : 1 ≤ k) (hkn : k ≤ n) :
    k ∣ lcmPrefix n := by
  exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hk₁, hkn⟩)

theorem lcmPrefix_dvd {m n : ℕ} (hmn : m ≤ n) : lcmPrefix m ∣ lcmPrefix n := by
  apply Finset.lcm_mono
  intro k hk
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2.trans hmn⟩

theorem lcmPrefix_dvd_succ (n : ℕ) : lcmPrefix n ∣ lcmPrefix (n + 1) := by
  apply Finset.lcm_mono
  intro k hk
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,
    (Finset.mem_Icc.mp hk).2.trans (Nat.le_succ n)⟩

theorem succ_dvd_lcmPrefix_succ (n : ℕ) : n + 1 ∣ lcmPrefix (n + 1) := by
  apply Finset.dvd_lcm (f := id)
  exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩

theorem lcmPrefix_pos (n : ℕ) : 0 < lcmPrefix n := by
  apply Nat.pos_of_ne_zero
  simp [lcmPrefix, Finset.lcm_eq_zero_iff]

theorem sqIntegral_betaCoeff {m : ℕ} (hm : m ≠ 0) : SqIntegral (betaCoeff m) m := by
  refine ⟨betaNumerator m, ?_⟩
  unfold betaCoeff
  field_simp

theorem sqIntegral_gammaCoeff {m : ℕ} (hm : m ≠ 0) : SqIntegral (gammaCoeff m) m := by
  refine ⟨gammaNumerator m, ?_⟩
  unfold gammaCoeff
  field_simp

theorem sqIntegral_lcmPrefix {m : ℕ} (hm : m ≠ 0) {q : ℚ}
    (hq : SqIntegral q m) : ∃ z : ℤ, (lcmPrefix m : ℚ) ^ 2 * q = z := by
  rcases hq with ⟨z, hz⟩
  have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  obtain ⟨k, hk⟩ := dvd_lcmPrefix hmpos le_rfl
  refine ⟨(k : ℤ) ^ 2 * z, ?_⟩
  rw [hk, Nat.cast_mul]
  calc
    ((m : ℚ) * (k : ℚ)) ^ 2 * q = (k : ℚ) ^ 2 * ((m : ℚ) ^ 2 * q) := by ring
    _ = (k : ℚ) ^ 2 * z := by rw [hz]
    _ = ((k : ℤ) ^ 2 * z : ℤ) := by norm_num

theorem betaNumerator_one : betaNumerator 1 = 1 := by
  norm_num [betaNumerator, chiMinusThreeInt_one]

theorem betaNumerator_two : betaNumerator 2 = -5 := by
  norm_num [betaNumerator, chiMinusThreeInt_one, chiMinusThreeInt_two]

theorem betaNumerator_three : betaNumerator 3 = 9 := by
  norm_num [betaNumerator, chiMinusThreeInt_zero, chiMinusThreeInt_one,
    chiMinusThreeInt_three]

theorem betaNumerator_four : betaNumerator 4 = -11 := by
  decide

theorem betaNumerator_five : betaNumerator 5 = 24 := by
  norm_num [betaNumerator, chiMinusThreeInt_one, chiMinusThreeInt_five]

end DirichletL

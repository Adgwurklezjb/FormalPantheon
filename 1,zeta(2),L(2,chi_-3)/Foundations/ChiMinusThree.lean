import Comparator.Statement

/-!
Arithmetic facts for the real character modulo 3 in CDT v2, Theorem A.
The Legendre-symbol bridge supplies Mathlib's canonical multiplicative API.
-/

namespace DirichletL

theorem chiMinusThree_mod_three (n : ℕ) :
    chiMinusThree (n % 3) = chiMinusThree n := by
  simp [chiMinusThree]

theorem chiMinusThree_three_dvd {n : ℕ} (h : 3 ∣ n) : chiMinusThree n = 0 := by
  simp [chiMinusThree, Nat.dvd_iff_mod_eq_zero.mp h]

theorem chiMinusThree_eq_one {n : ℕ} (h : n % 3 = 1) : chiMinusThree n = 1 := by
  simp [chiMinusThree, h]

theorem chiMinusThree_eq_neg_one {n : ℕ} (h : n % 3 = 2) :
    chiMinusThree n = -1 := by
  simp [chiMinusThree, h]

/-- The character of CDT v2, Theorem A, equals Mathlib's Legendre symbol at 3. -/
theorem chiMinusThree_eq_legendreSym (n : ℕ) :
    chiMinusThree n = (legendreSym 3 (n : ℤ) : ℝ) := by
  have hmod : legendreSym 3 (n : ℤ) = legendreSym 3 ((n % 3 : ℕ) : ℤ) := by
    simpa only [Int.natCast_mod, Nat.cast_ofNat] using (legendreSym.mod 3 (n : ℤ))
  rw [hmod]
  have hlt := Nat.mod_lt n (by decide : 0 < 3)
  have hn : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hn with h | h | h <;> norm_num [chiMinusThree, h]

theorem chiMinusThree_mul (m n : ℕ) :
    chiMinusThree (m * n) = chiMinusThree m * chiMinusThree n := by
  simp [chiMinusThree_eq_legendreSym, Nat.cast_mul, legendreSym.mul]

theorem norm_chiMinusThree_le_one (n : ℕ) : ‖chiMinusThree n‖ ≤ 1 := by
  unfold chiMinusThree
  split_ifs <;> norm_num

/-- The integer-valued canonical character used in the q-series divisor sums. -/
def chiMinusThreeInt (n : ℕ) : ℤ := legendreSym 3 (n : ℤ)

theorem chiMinusThreeInt_cast (n : ℕ) :
    (chiMinusThreeInt n : ℝ) = chiMinusThree n := by
  simp [chiMinusThreeInt, chiMinusThree_eq_legendreSym]

theorem chiMinusThreeInt_zero : chiMinusThreeInt 0 = 0 := by
  have h := chiMinusThreeInt_cast 0
  norm_num [chiMinusThree] at h ⊢
  exact_mod_cast h

theorem chiMinusThreeInt_one : chiMinusThreeInt 1 = 1 := by
  have h := chiMinusThreeInt_cast 1
  norm_num [chiMinusThree] at h ⊢
  exact_mod_cast h

theorem chiMinusThreeInt_two : chiMinusThreeInt 2 = -1 := by
  have h := chiMinusThreeInt_cast 2
  norm_num [chiMinusThree] at h ⊢
  exact_mod_cast h

theorem chiMinusThreeInt_three : chiMinusThreeInt 3 = 0 := by
  have h := chiMinusThreeInt_cast 3
  norm_num [chiMinusThree] at h ⊢
  exact_mod_cast h

theorem chiMinusThreeInt_four : chiMinusThreeInt 4 = 1 := by
  have h := chiMinusThreeInt_cast 4
  norm_num [chiMinusThree] at h ⊢
  exact_mod_cast h

theorem chiMinusThreeInt_five : chiMinusThreeInt 5 = -1 := by
  have h := chiMinusThreeInt_cast 5
  norm_num [chiMinusThree] at h ⊢
  exact_mod_cast h

theorem chiMinusThreeInt_mul (m n : ℕ) :
    chiMinusThreeInt (m * n) = chiMinusThreeInt m * chiMinusThreeInt n := by
  simp only [chiMinusThreeInt, Nat.cast_mul, legendreSym.mul]

theorem norm_chiMinusThreeInt_complex_le_one (n : ℕ) :
    ‖(chiMinusThreeInt n : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast, chiMinusThreeInt_cast, ← Real.norm_eq_abs]
  exact norm_chiMinusThree_le_one n

end DirichletL

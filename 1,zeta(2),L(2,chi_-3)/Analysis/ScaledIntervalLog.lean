import Analysis.ScaledIntervalDivision
import Analysis.LogarithmOddSeries

/-!
Exact logarithm evaluation for CDT v2's contour profile, TeX 6947-6948 and 8384-8404.
-/

namespace DirichletL.ScaledInterval

/-- Enlarge a real interval by an integer error radius. -/
def inflate (e : ℤ) (I : NonemptyInterval ℤ) : NonemptyInterval ℤ :=
  I + (NonemptyInterval.pure (-e) ⊔ NonemptyInterval.pure e)

theorem inflate_mem {D : ℕ} (hD : 0 < D) {I : NonemptyInterval ℤ} {x x0 : ℝ} {e : ℤ}
    (hx0 : x0 ∈ denote D I) (he : |x - x0| ≤ (e : ℝ) / D) :
    x ∈ denote D (inflate e I) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hd : x - x0 ∈ denote D (NonemptyInterval.pure (-e) ⊔ NonemptyInterval.pure e) := by
    apply mem_denote_hull hD
    · have hl : ((-e : ℤ) : ℝ) / D ≤ x - x0 := by
        simpa only [Int.cast_neg, neg_div] using (abs_le.mp he).1
      simpa only [mul_comm] using (div_le_iff₀ hDr).mp hl
    · simpa only [mul_comm] using (le_div_iff₀ hDr).mp (abs_le.mp he).2
  have heq : x0 + (x - x0) = x := by ring
  simpa only [heq] using add_mem hD hx0 hd

/-- An odd power and the logarithmic partial sum, computed together. -/
def logOddTaylor (D : ℕ) (U : NonemptyInterval ℤ) :
    ℕ → NonemptyInterval ℤ × NonemptyInterval ℤ
  | 0 => (U, 0)
  | n + 1 =>
    let S := logOddTaylor D U n
    (mul D S.1 (square D U), S.2 + mul D (rational D 2 (2 * n + 1)) S.1)

theorem logOddTaylor_mem {D : ℕ} (hD : 0 < D) {U : NonemptyInterval ℤ} {u : ℝ}
    (hu : u ∈ denote D U) (n : ℕ) :
    u ^ (2 * n + 1) ∈ denote D (logOddTaylor D U n).1 ∧
      logOddPartial n u ∈ denote D (logOddTaylor D U n).2 := by
  induction n with
  | zero =>
    constructor
    · simpa only [logOddTaylor, Nat.mul_zero, Nat.zero_add, pow_one] using hu
    · simp [logOddTaylor, logOddPartial, denote]
  | succ n ih =>
    constructor
    · have heq : u ^ (2 * (n + 1) + 1) = u ^ (2 * n + 1) * u ^ 2 := by
        rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add]
      simpa only [logOddTaylor, heq] using mul_mem hD ih.1 (square_mem hD hu)
    · have hc : (2 : ℝ) * (1 / (2 * (n : ℝ) + 1)) ∈
          denote D (rational D 2 (2 * n + 1)) := by
        convert rational_mem hD 2 (2 * n + 1) (by positivity) using 1
        push_cast
        ring
      simpa only [logOddTaylor, logOddPartial, Finset.sum_range_succ] using
        add_mem hD ih.2 (mul_mem hD hc ih.1)

/-- Fourteen odd terms for an input interval contained in the real interval `[1,2]`. -/
def logReduced (D : ℕ) (I : NonemptyInterval ℤ) : NonemptyInterval ℤ :=
  let U := mul D (I - rational D 1 1) (inv D (I + rational D 1 1))
  inflate (rational D 1 (116 * 3 ^ 27)).snd (logOddTaylor D U 14).2

theorem logReduced_mem {D : ℕ} (hD : 0 < D) {I : NonemptyInterval ℤ} {x : ℝ}
    (hI : (D : ℤ) ≤ I.fst) (hI2 : I.snd ≤ 2 * (D : ℤ)) (hx : x ∈ denote D I) :
    Real.log x ∈ denote D (logReduced D I) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hxr := (mem_denote_iff hD).mp hx
  have hxl : (D : ℝ) ≤ (I.fst : ℝ) := by exact_mod_cast hI
  have hxu : (I.snd : ℝ) ≤ 2 * (D : ℝ) := by exact_mod_cast hI2
  have hx1 : 1 ≤ x := (mul_le_mul_left hDr).mp (by simpa only [mul_one] using hxl.trans hxr.1)
  have hx2 : x ≤ 2 := (mul_le_mul_left hDr).mp (by simpa only [mul_comm] using hxr.2.trans hxu)
  have hden : 0 < (I + rational D 1 1).fst := by
    simp [rational, NonemptyInterval.fst_natCast]
    omega
  have hone : (1 : ℝ) ∈ denote D (rational D 1 1) := by
    simpa only [Int.cast_one, div_one] using rational_mem hD 1 1 (by norm_num)
  have hu : (x - 1) / (x + 1) ∈ denote D
      (mul D (I - rational D 1 1) (inv D (I + rational D 1 1))) := by
    simpa only [div_eq_mul_inv] using
      mul_mem hD (sub_mem hD hx hone) (inv_mem hD hden (add_mem hD hx hone))
  have he : (1 / (116 * 3 ^ 27) : ℝ) ∈ denote D (rational D 1 (116 * 3 ^ 27)) := by
    convert rational_mem hD 1 (116 * 3 ^ 27) (by norm_num) using 1
    norm_num
  exact inflate_mem hD (logOddTaylor_mem hD hu 14).2
    ((abs_log_sub_logOddPartial_fourteen_le hx1 hx2).trans he.2)

/-- A logarithm-of-two enclosure at the same integer scale. -/
def logTwo (D : ℕ) : NonemptyInterval ℤ := logReduced D (rational D 2 1)

theorem logTwo_mem {D : ℕ} (hD : 0 < D) : Real.log 2 ∈ denote D (logTwo D) := by
  apply logReduced_mem hD
  · norm_num [rational]
    omega
  · norm_num [rational]
  · simpa only [Int.cast_ofNat, Int.cast_one, div_one] using rational_mem hD 2 1 (by norm_num)

/-- Add the signed logarithmic contribution of an integer power of two. -/
def logScaled (D : ℕ) (k : ℤ) (I : NonemptyInterval ℤ) : NonemptyInterval ℤ :=
  logReduced D I + mul D (rational D k 1) (logTwo D)

theorem logScaled_mem {D : ℕ} (hD : 0 < D) (k : ℤ) {I : NonemptyInterval ℤ} {y : ℝ}
    (hI : (D : ℤ) ≤ I.fst) (hI2 : I.snd ≤ 2 * (D : ℤ)) (hy : y ∈ denote D I) :
    Real.log ((2 : ℝ) ^ k * y) ∈ denote D (logScaled D k I) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hypos : 0 < y := by
    apply (mul_pos_iff_of_pos_left hDr).1
    exact hDr.trans_le ((show (D : ℝ) ≤ I.fst by exact_mod_cast hI).trans
      ((mem_denote_iff hD).mp hy).1)
  have hk : (k : ℝ) ∈ denote D (rational D k 1) := by
    simpa only [Int.cast_one, div_one] using rational_mem hD k 1 (by norm_num)
  rw [Real.log_mul (zpow_pos (by norm_num : (0 : ℝ) < 2) k).ne' hypos.ne', Real.log_zpow]
  simpa only [add_comm] using
    add_mem hD (logReduced_mem hD hI hI2 hy) (mul_mem hD hk (logTwo_mem hD))

end DirichletL.ScaledInterval

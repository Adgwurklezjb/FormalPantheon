import Analysis.ScaledRectangleNorm

/-!
Exact exponential evaluation for CDT's contour inputs (author revision, A.4, page 204).
The finite recurrence and error meanings are in
-/

namespace DirichletL.ScaledRectangle

/-- Enlarge both coordinates by an integer error radius. -/
def inflate (e : ℤ) (Z : ScaledRectangle) : ScaledRectangle :=
  let I := NonemptyInterval.pure (-e) ⊔ NonemptyInterval.pure e
  Z + (I, I)

theorem inflate_mem {D : ℕ} (hD : 0 < D) {Z : ScaledRectangle} {z z0 : ℂ} {e : ℤ}
    (hz0 : z0 ∈ denote D Z) (he : ‖z - z0‖ ≤ (e : ℝ) / D) :
    z ∈ denote D (inflate e Z) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  let I := NonemptyInterval.pure (-e) ⊔ NonemptyInterval.pure e
  have hc {t : ℝ} (ht : |t| ≤ (e : ℝ) / D) : t ∈ ScaledInterval.denote D I := by
    apply ScaledInterval.mem_denote_hull hD
    · have hl : ((-e : ℤ) : ℝ) / D ≤ t := by
        simpa only [Int.cast_neg, neg_div] using (abs_le.mp ht).1
      simpa only [mul_comm] using (div_le_iff₀ hDr).mp hl
    · simpa only [mul_comm] using (le_div_iff₀ hDr).mp (abs_le.mp ht).2
  have hd : z - z0 ∈ denote D (I, I) :=
    ⟨hc ((Complex.abs_re_le_norm _).trans he), hc ((Complex.abs_im_le_norm _).trans he)⟩
  have heq : z0 + (z - z0) = z := by ring
  simpa only [heq] using add_mem hD hz0 hd

/-- The next Taylor term and the sum of the preceding terms, computed together. -/
def expTaylor (D : ℕ) (Z : ScaledRectangle) : ℕ → ScaledRectangle × ScaledRectangle
  | 0 => (rational D 1 1, rational D 0 1)
  | n + 1 =>
    let S := expTaylor D Z n
    (realMul D (ScaledInterval.rational D 1 (n + 1)) (mul D S.1 Z), S.2 + S.1)

theorem expTaylor_mem {D : ℕ} (hD : 0 < D) {Z : ScaledRectangle} {z : ℂ}
    (hz : z ∈ denote D Z) (n : ℕ) :
    z ^ n / (n.factorial : ℂ) ∈ denote D (expTaylor D Z n).1 ∧
      (∑ m ∈ Finset.range n, z ^ m / (m.factorial : ℂ)) ∈
        denote D (expTaylor D Z n).2 := by
  induction n with
  | zero =>
    constructor
    · simpa only [expTaylor, pow_zero, Nat.factorial_zero, Nat.cast_one, Int.cast_one, div_one]
        using rational_mem hD 1 1 (by norm_num)
    · simpa only [expTaylor, Finset.sum_range_zero, Int.cast_zero, Int.cast_one, zero_div]
        using rational_mem hD 0 1 (by norm_num)
  | succ n ih =>
    have hc : 1 / ((n + 1 : ℕ) : ℝ) ∈
        ScaledInterval.denote D (ScaledInterval.rational D 1 (n + 1)) := by
      simpa only [Int.cast_one, Int.cast_add, Int.cast_natCast, Nat.cast_add, Nat.cast_one]
        using ScaledInterval.rational_mem hD 1 (n + 1) (by positivity)
    have ht := realMul_mem hD hc (mul_mem hD ih.1 hz)
    have heq : ((1 / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
        (z ^ n / (n.factorial : ℂ) * z) = z ^ (n + 1) / ((n + 1).factorial : ℂ) := by
      push_cast
      rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      field_simp
      push_cast
      ring
    constructor
    · simpa only [expTaylor, heq] using ht
    · simpa only [expTaylor, Finset.sum_range_succ] using add_mem hD ih.2 ih.1

/-- Forty-eight Taylor terms with the exact remainder for inputs of norm at most four. -/
def exp48 (D : ℕ) (Z : ScaledRectangle) : ScaledRectangle :=
  inflate (ScaledInterval.rational D (2 * 4 ^ 48) (Nat.factorial 48)).snd
    (expTaylor D Z 48).2

theorem exp48_mem {D : ℕ} (hD : 0 < D) {Z : ScaledRectangle} {z : ℂ}
    (hz : z ∈ denote D Z) (hz4 : ‖z‖ ≤ 4) :
    Complex.exp z ∈ denote D (exp48 D Z) := by
  have hb := Complex.exp_bound' (x := z) (n := 48)
    ((div_le_iff₀ (by norm_num)).2 (by norm_num; linarith))
  have he : (2 * (4 : ℝ) ^ 48 / (Nat.factorial 48 : ℝ)) ∈
      ScaledInterval.denote D (ScaledInterval.rational D (2 * 4 ^ 48) (Nat.factorial 48)) := by
    convert ScaledInterval.rational_mem hD (2 * 4 ^ 48) (Nat.factorial 48)
      (by positivity) using 1
    norm_num
  apply inflate_mem hD (expTaylor_mem hD hz 48).2
  calc
    _ ≤ ‖z‖ ^ 48 / (Nat.factorial 48 : ℝ) * 2 := hb
    _ ≤ (4 : ℝ) ^ 48 / (Nat.factorial 48 : ℝ) * 2 := by gcongr
    _ = 2 * (4 : ℝ) ^ 48 / (Nat.factorial 48 : ℝ) := by ring
    _ ≤ _ := he.2

end DirichletL.ScaledRectangle

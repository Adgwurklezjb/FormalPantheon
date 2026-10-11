import Comparator.Statement

/-!
Exact consecutive-block rounding bounds for CDT v2, supplied TeX 3998-4028
and 4150-4179. Declaration meanings and integral-endpoint checks precede
-/

namespace DirichletL

/-- The natural size of the interval between two adjacent integer cuts. -/
def consecutiveBlockSize {s : ℕ} (c : Fin (s + 1) → ℕ) (q : Fin s) : ℕ :=
  c q.succ - c q.castSucc

theorem abs_consecutiveBlockSize_sub_mul_sub_le_one {s d : ℕ}
    {c : Fin (s + 1) → ℕ} {a : Fin (s + 1) → ℝ}
    (hc : Monotone c)
    (hcut : ∀ r, (c r : ℝ) ≤ a r * d ∧ a r * d ≤ (c r : ℝ) + 1)
    (q : Fin s) :
    |(consecutiveBlockSize c q : ℝ) - (a q.succ - a q.castSucc) * d| ≤ 1 := by
  have hle := hc (Fin.castSucc_lt_succ q).le
  rw [consecutiveBlockSize, Nat.cast_sub hle]
  apply abs_le.mpr
  constructor <;> nlinarith [(hcut q.succ).1, (hcut q.succ).2,
    (hcut q.castSucc).1, (hcut q.castSucc).2]

theorem consecutiveBlockSize_ge_half_width {n d : ℕ} {w p : ℝ}
    (hw : 0 < w) (hwp : w ≤ p)
    (happrox : |(n : ℝ) - p * d| ≤ 1) (hthreshold : 2 / w ≤ (d : ℝ)) :
    (w / 2) * d ≤ (n : ℝ) := by
  have hd : 0 < (d : ℝ) := lt_of_lt_of_le (by positivity) hthreshold
  have hwd : 2 ≤ (d : ℝ) * w := (div_le_iff₀ hw).mp hthreshold
  have hmul := mul_le_mul_of_nonneg_right hwp hd.le
  have hlow := (abs_le.mp happrox).1
  nlinarith

end DirichletL

import Analysis.LevelTwoLogVariation

/-!
Finite recurrences for CDT v2's product profile, TeX 6947-6948 and 8384-8404.
Meanings and total-function edge cases precede these bodies in
-/

namespace DirichletL

theorem levelTwoLogPartial_succ (n : ℕ) (q : ℂ) :
    levelTwoLogPartial (n + 1) q = levelTwoLogPartial n q +
      24 * Real.log ‖1 + q ^ (n + 1)‖ := by
  simp only [levelTwoLogPartial, Finset.sum_range_succ, Complex.add_re, Complex.log_re]
  ring

theorem levelTwoLogSlope_succ (n : ℕ) (q : ℂ) :
    levelTwoLogSlope (n + 1) q = levelTwoLogSlope n q +
      24 * ((n + 1 : ℕ) : ℂ) * q ^ n / (1 + q ^ (n + 1)) := by
  simp only [levelTwoLogSlope, Finset.sum_range_succ]
  ring

end DirichletL

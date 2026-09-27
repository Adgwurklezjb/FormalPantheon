import Mathlib

/-!
Review-facing statement file for the Dirichlet L-value formalization.

The definitions in this file are deliberately self-contained: the review
surface imports only Mathlib and exposes the exact real-valued statement.
-/

namespace DirichletL

/-- The character in CDT v2, Theorem A, written by its residue class. -/
def chiMinusThree (n : ℕ) : ℝ :=
  if n % 3 = 0 then 0 else if n % 3 = 1 then 1 else -1

theorem chiMinusThree_zero : chiMinusThree 0 = 0 := by
  simp [chiMinusThree]

theorem chiMinusThree_one : chiMinusThree 1 = 1 := by
  norm_num [chiMinusThree]

theorem chiMinusThree_two : chiMinusThree 2 = -1 := by
  norm_num [chiMinusThree]

/-- The positive-integer zeta series in CDT v2, lemma `defabc`, part (3). -/
noncomputable def zetaTwo : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else 1 / (n : ℝ) ^ 2

/-- The real L-value in CDT v2, Theorem A; the zero-index summand is zero. -/
noncomputable def lTwoChiMinusThree : ℝ :=
  ∑' n : ℕ, chiMinusThree n / (n : ℝ) ^ 2

/-- The target proposition from CDT v2, Theorem A, in the zeta normalization. -/
def MainTheorem : Prop :=
  ∀ a b c : ℚ,
    (a : ℝ) + (b : ℝ) * zetaTwo + (c : ℝ) * lTwoChiMinusThree = 0 →
      a = 0 ∧ b = 0 ∧ c = 0

/-- The standard finite-family formulation of the same assertion. -/
def standardLinearIndependent : Prop :=
  LinearIndependent ℚ ![(1 : ℝ), zetaTwo, lTwoChiMinusThree]

/-- The coefficient form of CDT v2, Theorem A, with its original pi-squared value. -/
def PiSquaredTheorem : Prop :=
  ∀ a b c : ℚ,
    (a : ℝ) + (b : ℝ) * Real.pi ^ 2 + (c : ℝ) * lTwoChiMinusThree = 0 →
      a = 0 ∧ b = 0 ∧ c = 0

theorem zetaTwo_eq_pi_sq_div_six : zetaTwo = Real.pi ^ 2 / 6 := by
  calc
    zetaTwo = ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
      unfold zetaTwo
      apply tsum_congr
      intro n
      by_cases hn : n = 0 <;> simp [hn]
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq

theorem mainTheorem_iff_linearIndependent :
    MainTheorem ↔ standardLinearIndependent := by
  constructor
  · intro h
    rw [standardLinearIndependent, Fintype.linearIndependent_iff]
    intro g hg i
    have hrel : (g 0 : ℝ) + (g 1 : ℝ) * zetaTwo +
        (g 2 : ℝ) * lTwoChiMinusThree = 0 := by
      simpa [Fin.sum_univ_succ, Rat.smul_def, add_assoc] using hg
    rcases h (g 0) (g 1) (g 2) hrel with ⟨h0, h1, h2⟩
    fin_cases i <;> assumption
  · intro h a b c habc
    have h' := (Fintype.linearIndependent_iff.mp h)
      (fun i : Fin 3 => match i with | 0 => a | 1 => b | 2 => c)
    have hsum : ∑ i : Fin 3,
        ((match i with | 0 => a | 1 => b | 2 => c) : ℚ) •
          (![ (1 : ℝ), zetaTwo, lTwoChiMinusThree] i) = 0 := by
      simpa [Fin.sum_univ_succ, Rat.smul_def, add_assoc] using habc
    have hz := h' hsum
    exact ⟨hz 0, hz 1, hz 2⟩

/-- Rational rescaling identifies the target with CDT v2, Theorem A. -/
theorem mainTheorem_iff_piSquaredTheorem : MainTheorem ↔ PiSquaredTheorem := by
  constructor
  · intro h a b c habc
    have hz := h a (6 * b) c (by
      rw [zetaTwo_eq_pi_sq_div_six]
      push_cast
      nlinarith [habc])
    exact ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩
  · intro h a b c habc
    have hz := h a (b / 6) c (by
      rw [zetaTwo_eq_pi_sq_div_six] at habc
      push_cast
      nlinarith [habc])
    exact ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩

end DirichletL

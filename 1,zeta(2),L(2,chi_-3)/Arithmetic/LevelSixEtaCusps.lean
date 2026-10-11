import Arithmetic.LevelSixEtaWords

/-!
Exact affine cusp certificates for the case C eta products in Zagier (2009),
Section 5, PDF page 8, and CDT v2 Section 11.1. The candidate word search
is not part of the proof; all matrix equalities use integer arithmetic.
-/

namespace DirichletL

/-- An affine argument and the S/T word used in a cusp transformation. -/
structure EtaCuspData where
  /-- The coefficient of the upper-half-plane variable in the affine numerator. -/
  numerator : ℕ
  /-- The integer translation in the affine numerator. -/
  offset : ℤ
  /-- The natural denominator of the affine argument. -/
  denominator : ℕ
  /-- The integer S/T word in the matrix certificate. -/
  word : List ℤ

/-- Affine data for the twelve representatives at the four eta scales. -/
def levelSixEtaCuspData : Fin 12 → Fin 4 → EtaCuspData :=
  ![![⟨1, 0, 1, []⟩,
      ⟨2, 0, 1, []⟩,
      ⟨3, 0, 1, []⟩,
      ⟨6, 0, 1, []⟩],
    ![⟨1, 0, 1, [0]⟩,
      ⟨1, 0, 2, [0]⟩,
      ⟨1, 0, 3, [0]⟩,
      ⟨1, 0, 6, [0]⟩],
    ![⟨1, 0, 1, [0, 1, 0, 0, 0]⟩,
      ⟨1, 1, 2, [0]⟩,
      ⟨1, 1, 3, [0]⟩,
      ⟨1, 1, 6, [0]⟩],
    ![⟨1, 0, 1, [0, 2, 0, 0, 0]⟩,
      ⟨1, 0, 2, [0, 1, 0, 0, 0]⟩,
      ⟨1, 2, 3, [0]⟩,
      ⟨1, 2, 6, [0]⟩],
    ![⟨1, 0, 1, [0, 3, 0, 0, 0]⟩,
      ⟨1, 1, 2, [0, 1, 0, 0, 0]⟩,
      ⟨1, 0, 3, [0, 1, 0, 0, 0]⟩,
      ⟨1, 3, 6, [0]⟩],
    ![⟨1, 0, 1, [0, 4, 0, 0, 0]⟩,
      ⟨1, 0, 2, [0, 2, 0, 0, 0]⟩,
      ⟨1, 1, 3, [0, 1, 0, 0, 0]⟩,
      ⟨1, 4, 6, [0]⟩],
    ![⟨1, 0, 1, [0, 5, 0, 0, 0]⟩,
      ⟨1, 1, 2, [0, 2, 0, 0, 0]⟩,
      ⟨1, 2, 3, [0, 1, 0, 0, 0]⟩,
      ⟨1, 5, 6, [0]⟩],
    ![⟨1, 0, 1, [0, -2, 0, 0]⟩,
      ⟨2, 0, 1, [1, 1, 0, 0, 0]⟩,
      ⟨1, 2, 3, [1, -2, -1, 0]⟩,
      ⟨2, 1, 3, [3]⟩],
    ![⟨1, 0, 1, [0, -2, 1, 0]⟩,
      ⟨2, 0, 1, [1, 3, 0, 0, 0]⟩,
      ⟨1, 0, 3, [1, -2, 0, 0]⟩,
      ⟨2, 0, 3, [3, 1, 0, 0, 0]⟩],
    ![⟨1, 0, 1, [0, -2, 2, 0]⟩,
      ⟨2, 0, 1, [1, 5, 0, 0, 0]⟩,
      ⟨1, 1, 3, [1, -2, 0, 0]⟩,
      ⟨2, 2, 3, [3, 1, 0, 0, 0]⟩],
    ![⟨1, 0, 1, [0, -3, 0, 0]⟩,
      ⟨1, 1, 2, [0, -1, 2, 0, 0]⟩,
      ⟨3, 0, 1, [1, 1, 0, 0, 0]⟩,
      ⟨3, 1, 2, [2]⟩],
    ![⟨1, 0, 1, [0, -1, 2, 1, 0]⟩,
      ⟨1, 0, 2, [1, -3, 0, 0]⟩,
      ⟨3, 0, 1, [2, 2, 0, 0, 0]⟩,
      ⟨3, 0, 2, [4, 1, 0, 0, 0]⟩]]

theorem levelSixEtaCuspData_numerator_pos (i : Fin 12) (j : Fin 4) :
    0 < (levelSixEtaCuspData i j).numerator := by
  fin_cases i <;> fin_cases j <;> decide

theorem levelSixEtaCuspData_denominator_pos (i : Fin 12) (j : Fin 4) :
    0 < (levelSixEtaCuspData i j).denominator := by
  fin_cases i <;> fin_cases j <;> decide

theorem levelSixEtaCuspData_matrix (i : Fin 12) (j : Fin 4) :
    !![(levelSixEtaScale j : ℤ), 0; 0, 1] *
        (levelSixRep i : Matrix (Fin 2) (Fin 2) ℤ) =
      (modularWordMatrix (levelSixEtaCuspData i j).word : Matrix (Fin 2) (Fin 2) ℤ) *
        !![((levelSixEtaCuspData i j).numerator : ℤ), (levelSixEtaCuspData i j).offset;
          0, ((levelSixEtaCuspData i j).denominator : ℤ)] := by
  fin_cases i <;> fin_cases j <;> decide

end DirichletL

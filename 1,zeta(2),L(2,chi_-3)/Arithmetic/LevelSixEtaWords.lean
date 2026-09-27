import Arithmetic.LevelSixMatrices
import Arithmetic.ModularWords

/-!
Exact scaled generator words for the eta quotient in CDT v2 Section 11.1,
equation `haupt`. The finite certificates use integer matrix arithmetic.
The word search that supplied the table is not part of the proof.
-/

namespace DirichletL

open scoped MatrixGroups

/-- The S and T families of level-six generators, respectively. -/
def levelSixEtaMatrix : Bool → Fin 12 → SL(2, ℤ)
  | false, i => levelSixRep i * ModularGroup.S * (levelSixRep (levelSixPermS i))⁻¹
  | true, i => levelSixRep i * ModularGroup.T * (levelSixRep (levelSixPermT i))⁻¹

/-- The four eta arguments occurring in the level-six Hauptmodul. -/
def levelSixEtaScale : Fin 4 → ℕ := ![1, 2, 3, 6]

theorem levelSixEtaScale_pos (j : Fin 4) : 0 < levelSixEtaScale j := by
  fin_cases j <;> decide

/-- Words for conjugating the level-six generators by each eta scale. -/
def levelSixEtaWord : Bool → Fin 12 → Fin 4 → List ℤ
  | false =>
    ![![[],
      [],
      [],
      []],
    ![[0, 0],
      [0, 0],
      [0, 0],
      [0, 0]],
    ![[0, 1, -5, 0, 0],
      [-1, 1, -2, 0, 0],
      [-2, 2, 1, 0, 0, 0],
      [-5, 1, 0, 0, 0]],
    ![[0, 2, -2, 2, 0, 0],
      [0, 1, -5, -1, 0],
      [-1, 4, -1, 0, 0, 0],
      [-2, 2, -2, 0, 0, 0]],
    ![[0, 6],
      [0, 3],
      [0, 2],
      [-1, -1, 0, 0, 0]],
    ![[0, 6],
      [0, 3],
      [0, 2],
      [-1, -1, 0, 0, 0]],
    ![[0, 6, 1, 0, 0, 0],
      [0, 3, 2, 0, 0, 0],
      [0, 2, 3, 0, 0, 0],
      [-1, 5, 0, 0, 0]],
    ![[0, -6, 0, 0],
      [0, -3, 0, 0],
      [0, -2, 0, 0],
      [1, 1, 0, 0, 0]],
    ![[0, -2, 2, -2, -1, 0, 0, 0],
      [0, -1, 5, -1, 0],
      [1, -4, -2, 0],
      [2, -2, -4, 0]],
    ![[0, -2, 2, -2],
      [0, -1, 5, 1, 0],
      [1, -4, 1, 0],
      [2, -2, 2, 0]],
    ![[0, -6, 0, 0],
      [0, -3, 0, 0],
      [0, -2, 0, 0],
      [1, 1, 0, 0, 0]],
    ![[0, -1, 1, -2, 2],
      [1, -6, -1, 0],
      [1, -1, 3, -1, 0],
      [3, -2, -3, 0]]]
  | true =>
    ![![[1, 0, 0, 0],
      [2, 0, 0, 0],
      [3, 0, 0, 0],
      [6, 0, 0, 0]],
    ![[],
      [],
      [],
      []],
    ![[],
      [],
      [],
      []],
    ![[],
      [],
      [],
      []],
    ![[],
      [],
      [],
      []],
    ![[],
      [],
      [],
      []],
    ![[0, 6, 0, 0],
      [0, 3, 0, 0],
      [0, 2, 0, 0],
      [-1, -1, 0]],
    ![[],
      [],
      [],
      []],
    ![[],
      [],
      [],
      []],
    ![[0, -2, 2, -2, -1, 0],
      [0, -1, 5, -1, 0, 0, 0],
      [1, -4, -2, 0, 0, 0],
      [2, -2, -4, 0, 0, 0]],
    ![[0, -6, -1, 0, 0, 0],
      [0, -3, -2, 0, 0, 0],
      [0, -2, -3, 0, 0, 0],
      [1, -5, 0]],
    ![[0, -1, 1, -2, 2, 0, 0],
      [1, -6, -1, 0, 0, 0],
      [1, -1, 3, -1, 0, 0, 0],
      [3, -2, -3, 0, 0, 0]]]

theorem levelSixEtaWord_matrix (b : Bool) (i : Fin 12) (j : Fin 4) :
    (modularWordMatrix (levelSixEtaWord b i j) : Matrix (Fin 2) (Fin 2) ℤ) *
        !![(levelSixEtaScale j : ℤ), 0; 0, 1] =
      !![(levelSixEtaScale j : ℤ), 0; 0, 1] *
        (levelSixEtaMatrix b i : Matrix (Fin 2) (Fin 2) ℤ) := by
  cases b <;> fin_cases i <;> fin_cases j <;> decide

theorem levelSixEtaWord_exponent (b : Bool) (i : Fin 12) :
    12 ∣ 2 * modularWordExponent (levelSixEtaWord b i 0) -
      4 * modularWordExponent (levelSixEtaWord b i 1) -
      2 * modularWordExponent (levelSixEtaWord b i 2) +
      4 * modularWordExponent (levelSixEtaWord b i 3) := by
  cases b <;> fin_cases i <;> decide

end DirichletL

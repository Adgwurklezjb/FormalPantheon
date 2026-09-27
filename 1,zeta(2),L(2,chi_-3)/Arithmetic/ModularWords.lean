import Mathlib

/-!
Finite words in S and integer powers of T, used to certify the eta
transformations underlying CDT v2 Section 11.1, equation `haupt`.
-/

namespace DirichletL

open scoped MatrixGroups

/-- The ordered product of T^n*S for a finite list of integer exponents. -/
def modularWordMatrix (w : List ℤ) : SL(2, ℤ) :=
  (w.map (fun n => ModularGroup.T ^ n * ModularGroup.S)).prod

/-- The eta-square multiplier exponent of a word with blocks T^n*S. -/
def modularWordExponent (w : List ℤ) : ℤ := (w.map (fun n => n - 3)).sum

end DirichletL

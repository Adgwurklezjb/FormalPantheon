import Proof.Main

/-! Closed solution interface for CDT Theorem A and its corollaries. -/

namespace DirichletL.Comparison

/-- The checked rational coefficient formulation of CDT Theorem A. -/
theorem mainTheorem : DirichletL.MainTheorem := DirichletL.mainTheorem

/-- The checked ordered-family formulation over the rationals. -/
theorem linearIndependent : DirichletL.standardLinearIndependent :=
  DirichletL.linearIndependent_one_zetaTwo_lTwoChiMinusThree

/-- The checked pi-squared formulation of CDT Theorem A. -/
theorem piSquaredTheorem : DirichletL.PiSquaredTheorem := DirichletL.piSquaredTheorem

/-- The checked irrationality consequence for the specified real L-value. -/
theorem irrational : Irrational DirichletL.lTwoChiMinusThree :=
  DirichletL.irrational_lTwoChiMinusThree

end DirichletL.Comparison

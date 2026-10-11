import Analysis.AuxiliaryFormalSeries

/-!
Scaling the literal auxiliary template of CDT v2, supplied TeX 3965-3998.
The scalar power and empty-dimension checks precede the proof in
-/

namespace DirichletL

theorem auxiliaryFormalSeries_smul_family {m : ℕ} (a : ℚ)
    (f : Fin m → PowerSeries ℚ) (h D : ℕ) (ε : ℝ)
    (t : ↥(auxiliaryFreeIndices m h D ε) → ℤ) :
    auxiliaryFormalSeries (fun i => a • f i) h D ε t =
      a ^ (m * h) • auxiliaryFormalSeries f h D ε t := by
  classical
  ext n
  rw [MvPowerSeries.coeff_smul, coeff_auxiliaryFormalSeries,
    coeff_auxiliaryFormalSeries, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs
  · simp only [PowerSeries.coeff_smul, smul_eq_mul, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  · simp

end DirichletL

import Analysis.LevelTwoOrbitBounds

/-!
The six modular representatives used in CDT author Lemma A.4.4, page 205.
Meanings and matrix normalization precede the bodies in
-/

namespace DirichletL

open Complex Function.Periodic
open _root_.UpperHalfPlane hiding I
open scoped MatrixGroups

/-- Integral representatives with lower row `(2, 2*n+1)`. -/
def levelTwoOrbitMatrix (n : ℤ) : SL(2, ℤ) :=
  ⟨!![1, n; 2, 2 * n + 1], by rw [Matrix.det_fin_two_of]; ring⟩

theorem qParam_one_T_zpow_smul (τ : ℍ) (m : ℤ) :
    Function.Periodic.qParam 1 (ModularGroup.T ^ m • τ : ℍ) =
      Function.Periodic.qParam 1 τ := by
  rw [ModularGroup.coe_T_zpow_smul_eq]
  simp only [qParam, Complex.ofReal_one, div_one]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨m, ?_⟩
  ring

theorem qParam_smul_eq_levelTwoOrbitMatrix (γ : SL(2, ℤ)) (τ : ℍ)
    (n : ℤ) (hc : γ 1 0 = 2) (hd : γ 1 1 = 2 * n + 1) :
    Function.Periodic.qParam 1 (γ • τ : ℍ) =
      Function.Periodic.qParam 1 (levelTwoOrbitMatrix n • τ : ℍ) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  rw [hc, hd] at hdet
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' (γ 0 0)
  · rw [hm] at hdet
    have hbad : 2 * (m * (2 * n + 1) - γ 0 1) = (1 : ℤ) := by nlinarith
    omega
  · rw [hm] at hdet
    have hb : γ 0 1 = n + m * (2 * n + 1) := by nlinarith
    have hfactor : γ = ModularGroup.T ^ m * levelTwoOrbitMatrix n := by
      apply Subtype.ext
      change γ.1 = (ModularGroup.T ^ m).1 * (levelTwoOrbitMatrix n).1
      rw [ModularGroup.coe_T_zpow]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [levelTwoOrbitMatrix, Matrix.mul_apply, Fin.sum_univ_two, hc, hd, hm, hb]
      ring
    rw [hfactor, mul_smul, qParam_one_T_zpow_smul]

theorem qParam_smul_eq_of_lower_left_eq_zero (γ : SL(2, ℤ)) (τ : ℍ)
    (hc : γ 1 0 = 0) :
    Function.Periodic.qParam 1 (γ • τ : ℍ) = Function.Periodic.qParam 1 τ := by
  obtain ⟨m, hm⟩ := ModularGroup.exists_eq_T_zpow_of_c_eq_zero hc
  rw [hm τ, qParam_one_T_zpow_smul]

theorem levelTwo_qParam_orbit_cases (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 2) (τ : ℍ)
    (hre : τ.re = 0) (hheight : τ.im ∈ Set.Icc (3 / 2) (8 / 5))
    (hnorm : ‖Function.Periodic.qParam 1 (γ • τ : ℍ)‖ ≤ 77 / 100) :
    Function.Periodic.qParam 1 (γ • τ : ℍ) = Function.Periodic.qParam 1 τ ∨
      ∃ n : ℤ, n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ) ∧
        Function.Periodic.qParam 1 (γ • τ : ℍ) =
          Function.Periodic.qParam 1 (levelTwoOrbitMatrix n • τ : ℍ) := by
  have hpos (δ : SL(2, ℤ)) (hc : δ 1 0 = 2)
      (hd : δ 1 1 = -5 ∨ δ 1 1 = -3 ∨ δ 1 1 = -1 ∨
        δ 1 1 = 1 ∨ δ 1 1 = 3 ∨ δ 1 1 = 5) :
      ∃ n : ℤ, n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ) ∧
        qParam 1 (δ • τ : ℍ) = qParam 1 (levelTwoOrbitMatrix n • τ : ℍ) := by
    let n : ℤ := (δ 1 1 - 1) / 2
    have hn : δ 1 1 = 2 * n + 1 := by
      dsimp only [n]
      omega
    have hmem : n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      dsimp only [n]
      omega
    exact ⟨n, hmem, qParam_smul_eq_levelTwoOrbitMatrix δ τ n hc hn⟩
  rcases levelTwo_lower_row_cases_of_qParam_norm_le γ hγ τ hre hheight hnorm with
    hc | ⟨hc, hd⟩
  · exact Or.inl (qParam_smul_eq_of_lower_left_eq_zero γ τ hc)
  · apply Or.inr
    rcases hc with hc | hc
    · have hnegc : (-γ) 1 0 = 2 := by change -(γ 1 0) = 2; omega
      have hnegd : (-γ) 1 1 = -5 ∨ (-γ) 1 1 = -3 ∨ (-γ) 1 1 = -1 ∨
          (-γ) 1 1 = 1 ∨ (-γ) 1 1 = 3 ∨ (-γ) 1 1 = 5 := by
        change -(γ 1 1) = -5 ∨ -(γ 1 1) = -3 ∨ -(γ 1 1) = -1 ∨
          -(γ 1 1) = 1 ∨ -(γ 1 1) = 3 ∨ -(γ 1 1) = 5
        omega
      obtain ⟨n, hmem, heq⟩ := hpos (-γ) hnegc hnegd
      exact ⟨n, hmem, by simpa only [ModularGroup.SL_neg_smul] using heq⟩
    · exact hpos γ hc hd

end DirichletL

import Mathlib

/-!
Exact height and lower-row bounds for CDT author Lemma A.4.4, page 205.
Meanings, rational comparisons, and endpoint checks precede the bodies in
-/

namespace DirichletL

open Complex Function.Periodic
open _root_.UpperHalfPlane hiding I
open scoped MatrixGroups

theorem lt_norm_qParam_one_of_im_le {τ : ℂ} (hτ : τ.im ≤ 3 / 74) :
    77 / 100 < ‖Function.Periodic.qParam 1 τ‖ := by
  have he : Real.exp (13 / 50) < 100 / 77 := by
    have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 13 / 50)
      (by norm_num) (n := 5) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hrecip : (77 / 100 : ℝ) < Real.exp (-(13 / 50)) := by
    calc
      _ = 1 / (100 / 77 : ℝ) := by norm_num
      _ < 1 / Real.exp (13 / 50) := one_div_lt_one_div_of_lt (Real.exp_pos _) he
      _ = Real.exp (-(13 / 50)) := by rw [Real.exp_neg, one_div]
  rw [Function.Periodic.norm_qParam, div_one]
  apply hrecip.trans_le
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hτ (show 0 ≤ 2 * Real.pi by positivity)
  linarith [Real.pi_lt_d2]

theorem im_levelTwo_smul_of_re_eq_zero (γ : SL(2, ℤ)) (τ : ℍ)
    (hτ : τ.re = 0) :
    (γ • τ : ℍ).im =
      τ.im / ((γ 1 0 : ℝ) ^ 2 * τ.im ^ 2 + (γ 1 1 : ℝ) ^ 2) := by
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, UpperHalfPlane.coe_re,
    hτ, Complex.intCast_im, mul_zero, zero_mul, sub_zero, zero_add, add_zero,
    Complex.add_im, Complex.mul_im, UpperHalfPlane.coe_im]
  congr 1
  ring

theorem odd_lower_right_of_mem_Gamma0_two (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 2) : Odd (γ 1 1) := by
  have hc := CongruenceSubgroup.Gamma0_mem.mp hγ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have hd0 : (γ 1 1 : ZMod 2) ≠ 0 := by
    intro hd
    have hz : (γ 0 0 : ZMod 2) * (γ 1 1 : ZMod 2) -
        (γ 0 1 : ZMod 2) * (γ 1 0 : ZMod 2) = 1 := by
      have h := congrArg (fun z : ℤ => (z : ZMod 2)) hdet
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_one] using h
    rw [hc, hd] at hz
    norm_num at hz
  have hone (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
    fin_cases x <;> norm_num at *
  have hd1 := hone (γ 1 1 : ZMod 2) hd0
  apply Int.odd_iff.mpr
  have h := (ZMod.intCast_eq_intCast_iff' (γ 1 1) 1 2).mp (by simpa using hd1)
  norm_num at h
  exact h

theorem abs_lower_left_lt_four_of_qParam_norm_le (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 2) (τ : ℍ)
    (hre : τ.re = 0) (hheight : 3 / 2 ≤ τ.im)
    (hnorm : ‖Function.Periodic.qParam 1 (γ • τ : ℍ)‖ ≤ 77 / 100) :
    |γ 1 0| < 4 := by
  by_contra! hc
  have hodd := Int.odd_iff.mp (odd_lower_right_of_mem_Gamma0_two γ hγ)
  have hdne : γ 1 1 ≠ 0 := by omega
  have hd : (1 : ℤ) ≤ |γ 1 1| := Int.one_le_abs hdne
  have hcR : (4 : ℝ) ≤ |(γ 1 0 : ℝ)| := by exact_mod_cast hc
  have hdR : (1 : ℝ) ≤ |(γ 1 1 : ℝ)| := by exact_mod_cast hd
  have hc2 : (16 : ℝ) ≤ (γ 1 0 : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hcR 2
    norm_num only [sq_abs] at h
    exact h
  have hd2 : (1 : ℝ) ≤ (γ 1 1 : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hdR 2
    norm_num only [sq_abs] at h
    exact h
  have hcprod := mul_le_mul_of_nonneg_right hc2 (sq_nonneg τ.im)
  have hpoly : 0 ≤ (2 * τ.im - 3) * (24 * τ.im - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hden : 0 < (γ 1 0 : ℝ) ^ 2 * τ.im ^ 2 + (γ 1 1 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (γ 1 0 : ℝ)) (sq_nonneg τ.im)]
  have him : (γ • τ : ℍ).im ≤ 3 / 74 := by
    rw [im_levelTwo_smul_of_re_eq_zero γ τ hre]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact (not_lt_of_ge hnorm) (lt_norm_qParam_one_of_im_le him)

theorem abs_lower_right_lt_seven_of_qParam_norm_le (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 2) (τ : ℍ)
    (hre : τ.re = 0) (hheight : τ.im ∈ Set.Icc (3 / 2) (8 / 5))
    (hc : γ 1 0 ≠ 0)
    (hnorm : ‖Function.Periodic.qParam 1 (γ • τ : ℍ)‖ ≤ 77 / 100) :
    |γ 1 1| < 7 := by
  by_contra! hd
  have hdiv : (2 : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) 2).mp
      (CongruenceSubgroup.Gamma0_mem.mp hγ)
  obtain ⟨k, hk⟩ := hdiv
  have hcabs : (2 : ℤ) ≤ |γ 1 0| := by
    rcases le_or_gt 0 (γ 1 0) with hp | hn
    · rw [abs_of_nonneg hp]
      omega
    · rw [abs_of_neg hn]
      omega
  have hcR : (2 : ℝ) ≤ |(γ 1 0 : ℝ)| := by exact_mod_cast hcabs
  have hdR : (7 : ℝ) ≤ |(γ 1 1 : ℝ)| := by exact_mod_cast hd
  have hc2 : (4 : ℝ) ≤ (γ 1 0 : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hcR 2
    norm_num only [sq_abs] at h
    exact h
  have hd2 : (49 : ℝ) ≤ (γ 1 1 : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7) hdR 2
    norm_num only [sq_abs] at h
    exact h
  have ht2 : (9 / 4 : ℝ) ≤ τ.im ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 2) hheight.1 2
    norm_num at h
    exact h
  have hcprod := mul_le_mul_of_nonneg_right hc2 (sq_nonneg τ.im)
  have hdenbound : (58 : ℝ) ≤
      (γ 1 0 : ℝ) ^ 2 * τ.im ^ 2 + (γ 1 1 : ℝ) ^ 2 := by nlinarith
  have hden : 0 < (γ 1 0 : ℝ) ^ 2 * τ.im ^ 2 + (γ 1 1 : ℝ) ^ 2 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 58) hdenbound
  have him : (γ • τ : ℍ).im ≤ 4 / 145 := by
    rw [im_levelTwo_smul_of_re_eq_zero γ τ hre]
    apply (div_le_iff₀ hden).mpr
    linarith only [hheight.2, hdenbound]
  exact (not_lt_of_ge hnorm)
    (lt_norm_qParam_one_of_im_le (him.trans (by norm_num)))

theorem levelTwo_lower_row_cases_of_qParam_norm_le (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 2) (τ : ℍ)
    (hre : τ.re = 0) (hheight : τ.im ∈ Set.Icc (3 / 2) (8 / 5))
    (hnorm : ‖Function.Periodic.qParam 1 (γ • τ : ℍ)‖ ≤ 77 / 100) :
    γ 1 0 = 0 ∨
      ((γ 1 0 = -2 ∨ γ 1 0 = 2) ∧
        (γ 1 1 = -5 ∨ γ 1 1 = -3 ∨ γ 1 1 = -1 ∨
          γ 1 1 = 1 ∨ γ 1 1 = 3 ∨ γ 1 1 = 5)) := by
  by_cases hc : γ 1 0 = 0
  · exact Or.inl hc
  have hcabs := abs_lower_left_lt_four_of_qParam_norm_le γ hγ τ hre hheight.1 hnorm
  have hdabs := abs_lower_right_lt_seven_of_qParam_norm_le γ hγ τ hre hheight hc hnorm
  have hcRange := abs_lt.mp hcabs
  have hdRange := abs_lt.mp hdabs
  have hodd := Int.odd_iff.mp (odd_lower_right_of_mem_Gamma0_two γ hγ)
  have hdiv : (2 : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) 2).mp
      (CongruenceSubgroup.Gamma0_mem.mp hγ)
  obtain ⟨k, hk⟩ := hdiv
  exact Or.inr ⟨by omega, by omega⟩

end DirichletL

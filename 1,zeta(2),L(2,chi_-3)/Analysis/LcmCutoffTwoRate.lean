import Mathlib

/-!
The continuous cutoff-two form of the harmonic rate in CDT v2,
supplied TeX 3363-3411 and 4480-4518. A finite sum of ramps keeps
the combined rate continuous at the harmonic index changes.
-/

namespace DirichletL

/-- The cutoff-two harmonic rate on a bounded interval, as a finite sum of ramps. -/
noncomputable def lcmCutoffTwoRate (B : ℕ) (t : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 B, min (max (t - 2 * (a : ℝ)) 0) 1 / (a : ℝ)

theorem lcmCutoffTwoRate_nonneg (B : ℕ) (t : ℝ) : 0 ≤ lcmCutoffTwoRate B t := by
  apply Finset.sum_nonneg
  intro a _
  exact div_nonneg (le_min (le_max_right _ _) zero_le_one) (Nat.cast_nonneg a)

theorem monotone_lcmCutoffTwoRate (B : ℕ) : Monotone (lcmCutoffTwoRate B) := by
  intro t u htu
  apply Finset.sum_le_sum
  intro a _
  exact div_le_div_of_nonneg_right
    (min_le_min (max_le_max (sub_le_sub_right htu _) le_rfl) le_rfl) (Nat.cast_nonneg a)

theorem continuous_lcmCutoffTwoRate (B : ℕ) : Continuous (lcmCutoffTwoRate B) := by
  unfold lcmCutoffTwoRate
  fun_prop

theorem lcmCutoffTwoRate_eq_zero (B : ℕ) {t : ℝ} (ht : t ≤ 2) :
    lcmCutoffTwoRate B t = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
  rw [max_eq_right (by linarith : t - 2 * (a : ℝ) ≤ 0)]
  norm_num

theorem lcmCutoffTwoRate_eq_harmonic {B : ℕ} {t : ℝ}
    (ht : 2 * (B : ℝ) + 1 ≤ t) : lcmCutoffTwoRate B t = (harmonic B : ℝ) := by
  rw [lcmCutoffTwoRate, harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_congr rfl
  intro a ha
  have haR : (a : ℝ) ≤ B := by exact_mod_cast (Finset.mem_Icc.mp ha).2
  have hone : 1 ≤ t - 2 * (a : ℝ) := by linarith
  rw [min_eq_right (hone.trans (le_max_left _ _)), one_div]

theorem lcmCutoffTwoRate_eq_of_le {A B : ℕ} {t : ℝ}
    (hAB : A ≤ B) (ht : t ≤ 2 * ((A : ℝ) + 1)) :
    lcmCutoffTwoRate B t = lcmCutoffTwoRate A t := by
  symm
  apply Finset.sum_subset
  · intro a ha
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1,
      (Finset.mem_Icc.mp ha).2.trans hAB⟩
  · intro a ha hnot
    have hAa : A + 1 ≤ a := by
      have ha1 := (Finset.mem_Icc.mp ha).1
      simp only [Finset.mem_Icc, not_and] at hnot
      omega
    have hAaR : (A : ℝ) + 1 ≤ a := by exact_mod_cast hAa
    rw [max_eq_right (by linarith : t - 2 * (a : ℝ) ≤ 0)]
    norm_num

theorem lcmCutoffTwoRate_on_cell {B j : ℕ} {t : ℝ} (hj : j < B)
    (hlo : 2 * (j : ℝ) + 1 ≤ t) (hhi : t ≤ 2 * (j : ℝ) + 3) :
    lcmCutoffTwoRate B t =
      (harmonic j : ℝ) + max (t / ((j : ℝ) + 1) - 2) 0 := by
  have htail : t ≤ 2 * (((j + 1 : ℕ) : ℝ) + 1) := by push_cast; linarith
  rw [lcmCutoffTwoRate_eq_of_le (Nat.succ_le_iff.mpr hj) htail]
  rw [lcmCutoffTwoRate, Finset.sum_Icc_succ_top (Nat.succ_pos j)]
  change lcmCutoffTwoRate j t +
    min (max (t - 2 * ((j + 1 : ℕ) : ℝ)) 0) 1 / ((j + 1 : ℕ) : ℝ) = _
  rw [lcmCutoffTwoRate_eq_harmonic hlo]
  have hden : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hmin : max (t - 2 * ((j + 1 : ℕ) : ℝ)) 0 ≤ 1 := by
    apply max_le
    · push_cast
      linarith
    · norm_num
  rw [min_eq_left hmin, Nat.cast_add, Nat.cast_one, ← max_div_div_right hden.le]
  have he : (t - 2 * ((j : ℝ) + 1)) / ((j : ℝ) + 1) =
      t / ((j : ℝ) + 1) - 2 := by field_simp
  rw [he, zero_div]

end DirichletL

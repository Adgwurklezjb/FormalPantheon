import Analysis.LcmCutoffTwoRate
import Arithmetic.LcmIntervalQuotientAsymptotic

/-!
Uniform scaling at the selected cutoff two in CDT v2, supplied TeX
4480-4518. Coordinates below the cutoff contribute the exact quotient
one, and the remaining coordinates use one shared PNT error threshold.
-/

namespace DirichletL

open Filter

theorem lcmIntervalQuotientMainTerm_eq_zero_of_le_cutoff {n k c : ℕ} (hnc : n ≤ c) :
    lcmIntervalQuotientMainTerm n k c = 0 := by
  by_cases hk : k = 0
  · subst k
    exact lcmIntervalQuotientMainTerm_zero_width n c
  have hidx : lcmIntervalQuotientIndex n k c = 0 := by
    apply Nat.div_eq_of_lt
    by_cases hn : n = 0
    · simpa only [hn, Nat.zero_sub] using
        (Nat.pos_of_ne_zero hk).trans_le (le_max_left k c)
    · exact (Nat.sub_lt (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hk)).trans_le
        (hnc.trans (le_max_right k c))
  simp only [lcmIntervalQuotientMainTerm, if_neg hk, hidx, harmonic_zero,
    Rat.cast_zero, Nat.cast_zero, zero_add, mul_zero, div_one]
  exact max_eq_right (sub_nonpos.mpr (by exact_mod_cast hnc))

theorem lcmIntervalQuotientMainTerm_cutoff_two {B D n : ℕ} (hD : 0 < D)
    (hn : n ≤ (2 * B + 2) * D) :
    lcmIntervalQuotientMainTerm n D (2 * D) / (D : ℝ) =
      lcmCutoffTwoRate B ((n : ℝ) / (D : ℝ)) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  by_cases hsmall : n ≤ 2 * D
  · have ht : (n : ℝ) / (D : ℝ) ≤ 2 := by
      apply (div_le_iff₀ hDR).mpr
      exact_mod_cast hsmall
    rw [lcmIntervalQuotientMainTerm_eq_zero_of_le_cutoff hsmall,
      lcmCutoffTwoRate_eq_zero B ht, zero_div]
  have hDn : D ≤ n := by omega
  let j := lcmIntervalQuotientIndex n D (2 * D)
  have hj : j = (n - D) / (2 * D) := by
    dsimp only [j, lcmIntervalQuotientIndex]
    rw [max_eq_right (by omega : D ≤ 2 * D)]
  have htwoD : 0 < 2 * D := by omega
  have hloN : j * (2 * D) ≤ n - D := by
    rw [hj]
    simpa only [Nat.mul_comm] using Nat.mul_div_le (n - D) (2 * D)
  have hhiN : n - D < (j + 1) * (2 * D) := by
    rw [hj]
    exact (Nat.div_lt_iff_lt_mul htwoD).mp (Nat.lt_succ_self _)
  have hloR : (j : ℝ) * (2 * (D : ℝ)) ≤ ((n - D : ℕ) : ℝ) := by
    exact_mod_cast hloN
  have hhiR : ((n - D : ℕ) : ℝ) < ((j : ℝ) + 1) * (2 * (D : ℝ)) := by
    exact_mod_cast hhiN
  rw [Nat.cast_sub hDn] at hloR hhiR
  have hlo : 2 * (j : ℝ) + 1 ≤ (n : ℝ) / (D : ℝ) := by
    apply (le_div_iff₀ hDR).mpr
    nlinarith only [hloR]
  have hhi : (n : ℝ) / (D : ℝ) < 2 * (j : ℝ) + 3 := by
    apply (div_lt_iff₀ hDR).mpr
    nlinarith only [hhiR]
  have htop : (n : ℝ) / (D : ℝ) ≤ 2 * (B : ℝ) + 2 := by
    apply (div_le_iff₀ hDR).mpr
    exact_mod_cast hn
  have hjB : j ≤ B := by
    by_contra h
    have hBj : B + 1 ≤ j := by omega
    have hBjR : (B : ℝ) + 1 ≤ j := by exact_mod_cast hBj
    linarith
  have hjden : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hmain : lcmIntervalQuotientMainTerm n D (2 * D) / (D : ℝ) =
      (harmonic j : ℝ) + max (((n : ℝ) / (D : ℝ)) / ((j : ℝ) + 1) - 2) 0 := by
    rw [lcmIntervalQuotientMainTerm, if_neg hD.ne']
    change ((D : ℝ) * (harmonic j : ℝ) +
      max ((n : ℝ) / ((j : ℝ) + 1) - ((2 * D : ℕ) : ℝ)) 0) / (D : ℝ) = _
    rw [add_div, ← max_div_div_right hDR.le]
    have hfirst : (D : ℝ) * (harmonic j : ℝ) / (D : ℝ) = (harmonic j : ℝ) := by
      field_simp
    have hlast : ((n : ℝ) / ((j : ℝ) + 1) - ((2 * D : ℕ) : ℝ)) / (D : ℝ) =
        ((n : ℝ) / (D : ℝ)) / ((j : ℝ) + 1) - 2 := by
      push_cast
      field_simp
    rw [hfirst, hlast, zero_div]
  rw [hmain]
  rcases lt_or_eq_of_le hjB with hjlt | hjeq
  · exact (lcmCutoffTwoRate_on_cell hjlt hlo hhi.le).symm
  · have hzero : ((n : ℝ) / (D : ℝ)) / ((j : ℝ) + 1) - 2 ≤ 0 := by
      apply sub_nonpos.mpr
      apply (div_le_iff₀ hjden).mpr
      rw [hjeq]
      linarith
    rw [max_eq_right hzero, add_zero, hjeq,
      lcmCutoffTwoRate_eq_harmonic (hjeq ▸ hlo)]

theorem eventually_abs_log_lcmIntervalQuotient_cutoff_two_le (B : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ D : ℕ in atTop, ∀ n ≤ (2 * B + 2) * D,
      |Real.log (lcmIntervalQuotient n D (2 * D) : ℝ) -
        (D : ℝ) * lcmCutoffTwoRate B ((n : ℝ) / (D : ℝ))| ≤ ε * (D : ℝ) := by
  let C : ℝ := ((2 * B + 2 : ℕ) : ℝ)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_abs_log_lcmIntervalQuotient_sub_mainTerm_le
      (one_div_pos.mpr hC) (div_pos hε hC))
  refine eventually_atTop.mpr ⟨max N 1, ?_⟩
  intro D hD n hn
  have hD0 : 0 < D := by omega
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD0
  by_cases hsmall : n ≤ 2 * D
  · have ht : (n : ℝ) / (D : ℝ) ≤ 2 := by
      apply (div_le_iff₀ hDR).mpr
      exact_mod_cast hsmall
    rw [lcmIntervalQuotient_eq_one_of_le_cutoff hsmall, Nat.cast_one, Real.log_one,
      lcmCutoffTwoRate_eq_zero B ht, mul_zero, sub_zero, abs_zero]
    exact mul_nonneg hε.le hDR.le
  have hDn : D ≤ n := by omega
  have hcn : 2 * D ≤ n := by omega
  have hNn : N ≤ n := by omega
  have hcap : (n : ℝ) ≤ C * (D : ℝ) := by
    dsimp only [C]
    exact_mod_cast hn
  have hγ : (1 / C) * (n : ℝ) ≤ (D : ℝ) := by
    have h : (n : ℝ) / C ≤ (D : ℝ) :=
      (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hcap)
    calc
      (1 / C) * (n : ℝ) = (n : ℝ) / C := by ring
      _ ≤ _ := h
  have he := hN n hNn D hDn (2 * D) hcn hγ
  have hm : lcmIntervalQuotientMainTerm n D (2 * D) =
      (D : ℝ) * lcmCutoffTwoRate B ((n : ℝ) / (D : ℝ)) := by
    have h := (div_eq_iff hDR.ne').mp (lcmIntervalQuotientMainTerm_cutoff_two hD0 hn)
    simpa only [mul_comm] using h
  rw [hm] at he
  calc
    _ ≤ (ε / C) * (n : ℝ) := he
    _ ≤ (ε / C) * (C * (D : ℝ)) :=
      mul_le_mul_of_nonneg_left hcap (div_nonneg hε.le hC.le)
    _ = _ := by field_simp

theorem eventually_log_lcmIntervalQuotient_floor_cutoff_two_le (B : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ D : ℕ in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ 2 * (B : ℝ) + 2 →
      Real.log (lcmIntervalQuotient ⌊t * (D : ℝ)⌋₊ D (2 * D) : ℝ) ≤
        (D : ℝ) * lcmCutoffTwoRate B t + ε * (D : ℝ) := by
  filter_upwards [eventually_abs_log_lcmIntervalQuotient_cutoff_two_le B hε,
    eventually_gt_atTop (0 : ℕ)] with D hD hD0 t ht0 ht
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD0
  have hn : ⌊t * (D : ℝ)⌋₊ ≤ (2 * B + 2) * D := by
    apply Nat.floor_le_of_le
    push_cast
    exact mul_le_mul_of_nonneg_right ht hDR.le
  have hr : ((⌊t * (D : ℝ)⌋₊ : ℕ) : ℝ) / (D : ℝ) ≤ t :=
    (div_le_iff₀ hDR).mpr (Nat.floor_le (mul_nonneg ht0 hDR.le))
  have he := (abs_le.mp (hD _ hn)).2
  calc
    _ ≤ (D : ℝ) * lcmCutoffTwoRate B (((⌊t * (D : ℝ)⌋₊ : ℕ) : ℝ) / (D : ℝ)) +
        ε * (D : ℝ) := by linarith only [he]
    _ ≤ _ := add_le_add_right
      (mul_le_mul_of_nonneg_left (monotone_lcmCutoffTwoRate B hr) hDR.le) _

end DirichletL

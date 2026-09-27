import Analysis.LcmCutoffTwoRate
import Analysis.Holonomy

/-!
The exact integral of the continuous cutoff-two rate in CDT v2,
supplied TeX 3462-3471 and 4480-4518. Each summand has a unit-length
linear ramp, whose exact area precedes the constant tail.
-/

namespace DirichletL

open MeasureTheory

theorem lcmCutoffTwoRate_le_harmonic (B : ℕ) (t : ℝ) :
    lcmCutoffTwoRate B t ≤ (harmonic B : ℝ) := by
  rw [lcmCutoffTwoRate, harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_le_sum
  intro a _
  simpa only [one_div] using
    div_le_div_of_nonneg_right (min_le_right (max (t - 2 * (a : ℝ)) 0) 1)
      (Nat.cast_nonneg a : (0 : ℝ) ≤ a)

theorem integral_lcmCutoffTwoRamp_fourteen {a : ℕ} (ha0 : 1 ≤ a) (ha6 : a ≤ 6) :
    (∫ t in (0 : ℝ)..14, min (max (t - 2 * (a : ℝ)) 0) 1 / (a : ℝ)) =
      (27 / 2 : ℝ) / (a : ℝ) - 2 := by
  have haR6 : (a : ℝ) ≤ 6 := by exact_mod_cast ha6
  let f : ℝ → ℝ := fun t => min (max (t - 2 * (a : ℝ)) 0) 1 / (a : ℝ)
  have hf : Continuous f := by dsimp only [f]; fun_prop
  have hzero : (∫ t in (0 : ℝ)..(2 * (a : ℝ)), f t) = 0 := by
    calc
      _ = ∫ _t in (0 : ℝ)..(2 * (a : ℝ)), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * (a : ℝ))] at ht
        dsimp only [f]
        rw [max_eq_right (sub_nonpos.mpr ht.2)]
        norm_num
      _ = _ := by simp
  have hlinear : (∫ t in (2 * (a : ℝ))..(2 * (a : ℝ) + 1), f t) =
      1 / (2 * (a : ℝ)) := by
    calc
      _ = ∫ t in (2 * (a : ℝ))..(2 * (a : ℝ) + 1),
          (t - 2 * (a : ℝ)) / (a : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by linarith : 2 * (a : ℝ) ≤ 2 * (a : ℝ) + 1)] at ht
        dsimp only [f]
        rw [max_eq_left (sub_nonneg.mpr ht.1),
          min_eq_left (by linarith only [ht.2] : t - 2 * (a : ℝ) ≤ 1)]
      _ = _ := by
        rw [intervalIntegral.integral_div,
          intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ => 2 * (a : ℝ))
            (continuous_id.intervalIntegrable _ _)
            intervalIntegrable_const,
          integral_id, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        field_simp
        ring
  have hconst : (∫ t in (2 * (a : ℝ) + 1)..14, f t) =
      (14 - (2 * (a : ℝ) + 1)) / (a : ℝ) := by
    calc
      _ = ∫ _t in (2 * (a : ℝ) + 1)..14, 1 / (a : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by linarith : 2 * (a : ℝ) + 1 ≤ 14)] at ht
        dsimp only [f]
        rw [min_eq_right ((show 1 ≤ t - 2 * (a : ℝ) by
          linarith only [ht.1]).trans (le_max_left _ _))]
      _ = _ := by rw [intervalIntegral.integral_const]; simp [smul_eq_mul, div_eq_mul_inv]
  have h01 : (∫ t in (0 : ℝ)..(2 * (a : ℝ)), f t) +
      (∫ t in (2 * (a : ℝ))..(2 * (a : ℝ) + 1), f t) =
        ∫ t in (0 : ℝ)..(2 * (a : ℝ) + 1), f t :=
    intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 (2 * (a : ℝ)))
    (hf.intervalIntegrable (2 * (a : ℝ)) (2 * (a : ℝ) + 1))
  have h14 : (∫ t in (0 : ℝ)..(2 * (a : ℝ) + 1), f t) +
      (∫ t in (2 * (a : ℝ) + 1)..14, f t) = ∫ t in (0 : ℝ)..14, f t :=
    intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 (2 * (a : ℝ) + 1))
    (hf.intervalIntegrable (2 * (a : ℝ) + 1) 14)
  change (∫ t in (0 : ℝ)..14, f t) = _
  rw [← h14, ← h01, hzero, hlinear, hconst]
  field_simp
  ring

theorem integral_lcmCutoffTwoRate_seven_fourteen :
    (∫ t in (0 : ℝ)..14, lcmCutoffTwoRate 7 t) = (843 / 40 : ℝ) := by
  have htail : (∫ t in (0 : ℝ)..14, lcmCutoffTwoRate 7 t) =
      ∫ t in (0 : ℝ)..14, lcmCutoffTwoRate 6 t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 14)] at ht
    apply lcmCutoffTwoRate_eq_of_le (by norm_num : (6 : ℕ) ≤ 7)
    norm_num
    exact ht.2
  rw [htail]
  simp only [lcmCutoffTwoRate]
  rw [intervalIntegral.integral_finset_sum (fun (a : ℕ) _ =>
    (show Continuous (fun t : ℝ => min (max (t - 2 * (a : ℝ)) 0) 1 / (a : ℝ)) by
      fun_prop).intervalIntegrable 0 14)]
  calc
    _ = ∑ a ∈ Finset.Icc 1 (6 : ℕ), ((27 / 2 : ℝ) / (a : ℝ) - 2) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact integral_lcmCutoffTwoRamp_fourteen (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2
    _ = _ := by
      norm_num [show Finset.Icc 1 (6 : ℕ) = {1, 2, 3, 4, 5, 6} by decide]

end DirichletL

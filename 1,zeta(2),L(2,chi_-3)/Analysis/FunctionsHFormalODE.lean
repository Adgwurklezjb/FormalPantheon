import Analysis.ZagierCaseCIdentification
import Analysis.NumeratorProductIdentity
import Analysis.QSeriesDifferential
import Analysis.FunctionsHODE

/-!
The forced equations of the literal H_B and H_C series in CDT v2,
Section 11.1, Lemma `defabc` and Proposition `functionsH`. The full
numerator products supply the forcing after formal operator transport.
-/

namespace DirichletL

local notation "H" => PowerSeries.map (Int.castRingHom ℚ) hauptmodul
local notation "f" => PowerSeries.map (Int.castRingHom ℚ) zagierEtaSeries

private theorem constantCoeff_H : PowerSeries.constantCoeff (R := ℚ) H = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_hauptmodul, map_zero]

private theorem coeff_one_H : PowerSeries.coeff (R := ℚ) 1 H = 1 := by
  simp only [PowerSeries.coeff_map, coeff_one_hauptmodul, map_one]

private theorem H_ne_zero : H ≠ 0 := by
  intro hz
  have hc := congrArg (PowerSeries.coeff (R := ℚ) 1) hz
  rw [coeff_one_H, map_zero] at hc
  exact one_ne_zero hc

private theorem f_ne_zero : f ≠ 0 := by
  intro hz
  have hc := congrArg (PowerSeries.coeff (R := ℚ) 0) hz
  rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_zagierEtaSeries, map_one, map_zero] at hc
  exact one_ne_zero hc

private theorem euler_H :
    powerSeriesEuler ℚ H = H * (1 - 10 * H + 9 * H ^ 2) * f ^ 2 := by
  have h := congrArg (PowerSeries.map (Int.castRingHom ℚ))
    powerSeriesEuler_hauptmodul_eq_etaSeries
  simpa only [hauptmodulK, nsmul_eq_mul, map_powerSeriesEuler, map_mul,
    map_sub, map_add, map_pow, map_ofNat, map_natCast, Nat.cast_ofNat, map_one] using h

private theorem euler_f_two :
    2 * (powerSeriesEuler ℚ f) ^ 2 -
        f * powerSeriesEuler ℚ (powerSeriesEuler ℚ f) =
      H * (1 - 10 * H + 9 * H ^ 2) * (9 * H - 3) * f ^ 6 := by
  have h := congrArg (PowerSeries.map (Int.castRingHom ℚ))
    zagierEtaSeries_second_identity
  simpa only [hauptmodulK, nsmul_eq_mul, map_powerSeriesEuler, map_mul,
    map_sub, map_add, map_pow, map_ofNat, map_natCast, Nat.cast_ofNat, map_one] using h

private theorem subst_h_series (V : PowerSeries ℚ) :
    MvPowerSeries.subst (fun (_ : Unit) => H)
        (zagierGenerating * MvPowerSeries.subst
          (fun (_ : Unit) => PowerSeries.map (Int.castRingHom ℚ) hauptmodulInverse) V) =
      f * V := by
  have hsH : MvPowerSeries.HasSubst (fun (_ : Unit) => H) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_H)
  have hJ0 : PowerSeries.constantCoeff (R := ℚ)
      (PowerSeries.map (Int.castRingHom ℚ) hauptmodulInverse) = 0 := by
    change (PowerSeries.constantCoeff (R := ℤ) hauptmodulInverse : ℚ) = 0
    simp only [constantCoeff_hauptmodulInverse, Int.cast_zero]
  have hsJ := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun (_ : Unit) => hJ0)
  have hJH : MvPowerSeries.subst (fun (_ : Unit) => H)
      (PowerSeries.map (Int.castRingHom ℚ) hauptmodulInverse) = PowerSeries.X := by
    rw [hauptmodulInverse, map_reversion, subst_reversion H constantCoeff_H coeff_one_H]
  rw [MvPowerSeries.subst_mul hsH, ← zagierEtaSeries_eq_subst_zagierGenerating,
    MvPowerSeries.subst_comp_subst_apply hsJ hsH, hJH]
  congr 1
  convert congrFun (MvPowerSeries.subst_self (σ := Unit) (R := ℚ)) V using 1

theorem subst_hB_hauptmodul :
    MvPowerSeries.subst (fun (_ : Unit) => H) hB = f * PowerSeries.mk betaCoeff :=
  subst_h_series (PowerSeries.mk betaCoeff)

theorem subst_hC_hauptmodul :
    MvPowerSeries.subst (fun (_ : Unit) => H) hC = f * PowerSeries.mk gammaCoeff :=
  subst_h_series (PowerSeries.mk gammaCoeff)

private theorem hSeries_ode_pullback (F V : PowerSeries ℚ)
    (hcomp : MvPowerSeries.subst (fun (_ : Unit) => H) F = f * V) :
    H * (1 - 10 * H + 9 * H ^ 2) * f ^ 3 *
        MvPowerSeries.subst (fun (_ : Unit) => H) (generatingODE F) =
      powerSeriesEuler ℚ (powerSeriesEuler ℚ V) :=
  subst_generatingODE_mul_of_euler_identities f F H V constantCoeff_H f_ne_zero
    hcomp euler_H euler_f_two

/-- The literal B-series has the constant forcing term one. -/
theorem hB_ode : generatingODE hB = 1 := by
  apply subst_injective_of_coeff_one H constantCoeff_H coeff_one_H
  have hsH : MvPowerSeries.HasSubst (fun (_ : Unit) => H) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_H)
  have h := hSeries_ode_pullback hB (PowerSeries.mk betaCoeff) subst_hB_hauptmodul
  rw [powerSeriesEuler_two_beta] at h
  have hb := congrArg (PowerSeries.map (Int.castRingHom ℚ)) betaNumerator_product_identity
  simp only [map_mul, map_sub, map_add, map_pow, map_ofNat, map_one] at hb
  rw [hb] at h
  have hKne : (1 - 10 * H + 9 * H ^ 2) ≠ 0 := by
    intro hz
    have h0 := congrArg (PowerSeries.constantCoeff (R := ℚ)) hz
    norm_num [constantCoeff_H] at h0
  have hc : MvPowerSeries.subst (fun (_ : Unit) => H) (generatingODE hB) = 1 := by
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero H_ne_zero hKne) (pow_ne_zero 3 f_ne_zero))
    simpa only [mul_one] using h
  simpa only [← MvPowerSeries.substAlgHom_apply hsH, map_one] using hc

/-- Clearing the geometric forcing of the literal C-series. -/
theorem one_sub_X_mul_hC_ode :
    (1 - PowerSeries.X) * generatingODE hC = 1 := by
  apply subst_injective_of_coeff_one H constantCoeff_H coeff_one_H
  have hsH : MvPowerSeries.HasSubst (fun (_ : Unit) => H) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_H)
  have hSX : (MvPowerSeries.substAlgHom hsH) (PowerSeries.X : PowerSeries ℚ) = H := by
    rw [MvPowerSeries.substAlgHom_apply]
    exact MvPowerSeries.subst_X hsH ()
  have h := hSeries_ode_pullback hC (PowerSeries.mk gammaCoeff) subst_hC_hauptmodul
  rw [powerSeriesEuler_two_gamma] at h
  have hg := congrArg (PowerSeries.map (Int.castRingHom ℚ)) gammaNumerator_product_identity
  simp only [map_mul, map_sub, map_add, map_pow, map_ofNat, map_one] at hg
  rw [hg] at h
  have hKne : (1 - 9 * H) ≠ 0 := by
    intro hz
    have h0 := congrArg (PowerSeries.constantCoeff (R := ℚ)) hz
    norm_num [constantCoeff_H] at h0
  have hc : (1 - H) *
      MvPowerSeries.subst (fun (_ : Unit) => H) (generatingODE hC) = 1 := by
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero H_ne_zero hKne) (pow_ne_zero 3 f_ne_zero))
    calc
      _ = H * (1 - 10 * H + 9 * H ^ 2) * f ^ 3 *
          MvPowerSeries.subst (fun (_ : Unit) => H) (generatingODE hC) := by ring
      _ = _ := by simpa only [mul_one] using h
  simpa only [← MvPowerSeries.substAlgHom_apply hsH, map_mul, map_sub, map_one, hSX] using hc

/-- Every coefficient of the C forcing is one, including degree zero. -/
theorem hC_ode : generatingODE hC = PowerSeries.mk 1 := by
  have hx : (1 - PowerSeries.X : PowerSeries ℚ) ≠ 0 := by
    intro hz
    have h0 := congrArg (PowerSeries.constantCoeff (R := ℚ)) hz
    simp at h0
  apply mul_left_cancel₀ hx
  calc
    _ = 1 := one_sub_X_mul_hC_ode
    _ = _ := by simpa only [mul_comm] using (PowerSeries.mk_one_mul_one_sub_eq_one ℚ).symm

/-- CDT's homogeneous positive-index recurrence for the literal b coefficients. -/
theorem hB_recurrence (n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℚ) ^ 2 * PowerSeries.coeff (R := ℚ) (n + 1) hB -
        (10 * (n : ℚ) * (n + 1 : ℚ) + 3) * PowerSeries.coeff (R := ℚ) n hB +
          9 * (n : ℚ) ^ 2 * PowerSeries.coeff (R := ℚ) (n - 1) hB = 0 := by
  have hs : generatingSeries (fun k => PowerSeries.coeff (R := ℚ) k hB) = hB := by
    ext k
    simp [generatingSeries]
  have h := congrArg (PowerSeries.coeff (R := ℚ) n) hB_ode
  rw [← hs, coeff_generatingODE] at h
  simpa [Nat.ne_of_gt hn] using h

/-- CDT's forced positive-index recurrence for the literal c coefficients. -/
theorem hC_recurrence (n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℚ) ^ 2 * PowerSeries.coeff (R := ℚ) (n + 1) hC -
        (10 * (n : ℚ) * (n + 1 : ℚ) + 3) * PowerSeries.coeff (R := ℚ) n hC +
          9 * (n : ℚ) ^ 2 * PowerSeries.coeff (R := ℚ) (n - 1) hC = 1 := by
  have hs : generatingSeries (fun k => PowerSeries.coeff (R := ℚ) k hC) = hC := by
    ext k
    simp [generatingSeries]
  have h := congrArg (PowerSeries.coeff (R := ℚ) n) hC_ode
  rw [← hs, coeff_generatingODE] at h
  simpa [Nat.ne_of_gt hn] using h

/-- The formal ODE of CDT's actual rational H combination, with all recurrences proved. -/
theorem generatingODE_h_linearCombination (a b c : ℚ) :
    generatingODE (a • hA + b • hB + c • hC) =
      generatingSeries (fun n => if n = 0 then b + c else c) := by
  have hs (F : PowerSeries ℚ) : generatingSeries (fun k => PowerSeries.coeff (R := ℚ) k F) = F := by
    ext k
    simp [generatingSeries]
  have hA0 : PowerSeries.coeff (R := ℚ) 1 hA - 3 * PowerSeries.coeff (R := ℚ) 0 hA = 0 := by
    norm_num [hA_coeff_one, hA_coeff_zero]
  have hB0 : PowerSeries.coeff (R := ℚ) 1 hB - 3 * PowerSeries.coeff (R := ℚ) 0 hB = 1 := by
    norm_num [hB_coeff_one, PowerSeries.coeff_zero_eq_constantCoeff_apply, hB_constantCoeff]
  have hC0 : PowerSeries.coeff (R := ℚ) 1 hC - 3 * PowerSeries.coeff (R := ℚ) 0 hC = 1 := by
    norm_num [hC_coeff_one, PowerSeries.coeff_zero_eq_constantCoeff_apply, hC_constantCoeff]
  have hArec (n : ℕ) (hn : 1 ≤ n) :
      (n + 1 : ℚ) ^ 2 * PowerSeries.coeff (R := ℚ) (n + 1) hA -
          (10 * (n : ℚ) * (n + 1 : ℚ) + 3) * PowerSeries.coeff (R := ℚ) n hA +
            9 * (n : ℚ) ^ 2 * PowerSeries.coeff (R := ℚ) (n - 1) hA = 0 := by
    have h := congrArg (PowerSeries.coeff (R := ℚ) n) hA_ode
    rw [← hs hA, coeff_generatingODE] at h
    simpa [Nat.ne_of_gt hn] using h
  simpa only [hs] using generatingODE_linearCombination_of_cdtRecurrences
    (fun n => PowerSeries.coeff (R := ℚ) n hA) (fun n => PowerSeries.coeff (R := ℚ) n hB)
    (fun n => PowerSeries.coeff (R := ℚ) n hC) a b c hA0 hArec hB0 hB_recurrence hC0 hC_recurrence

end DirichletL

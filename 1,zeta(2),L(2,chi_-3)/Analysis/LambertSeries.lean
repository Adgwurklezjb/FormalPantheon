import Arithmetic.PowerSeriesEuler
import Analysis.Hauptmodul

/-!
Exact Lambert factors for logarithmic differentiation of CDT v2, Section 11.1,
equation `haupt` (TeX lines 7619-7637). All statements are formal over Z;
-/

namespace DirichletL

theorem coeff_oneSubInv {k : ℕ} (hk : 0 < k) (n : ℕ) :
    PowerSeries.coeff (R := ℤ) n (oneSubInv k) = if k ∣ n then 1 else 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hnk : n < k
    · rw [coeff_oneSubInv_of_lt hnk]
      by_cases hn : n = 0
      · simp [hn]
      · have hnot : ¬ k ∣ n := fun h => hn (Nat.eq_zero_of_dvd_of_lt h hnk)
        simp [hn, hnot]
    · have hkn : k ≤ n := Nat.le_of_not_gt hnk
      have hn : n ≠ 0 := by omega
      have he := congrArg (PowerSeries.coeff (R := ℤ) n) (oneSubInv_rightInv hk)
      rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', if_pos hkn,
        PowerSeries.coeff_one, if_neg hn] at he
      rw [sub_eq_zero.mp he, ih (n - k) (by omega)]
      simp only [Nat.dvd_sub_iff_left hkn (dvd_refl k)]

/-- The formal logarithmic factor k*X^k/(1-X^k). -/
noncomputable def lambertLogFactor (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.C (R := ℤ) (k : ℤ) * PowerSeries.X ^ k * oneSubInv k

theorem coeff_lambertLogFactor {k : ℕ} (hk : 0 < k) (n : ℕ) :
    PowerSeries.coeff (R := ℤ) n (lambertLogFactor k) =
      if n = 0 then 0 else if k ∣ n then (k : ℤ) else 0 := by
  rw [lambertLogFactor, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul']
  by_cases hkn : k ≤ n
  · rw [if_pos hkn, coeff_oneSubInv hk]
    have hn : n ≠ 0 := by omega
    simp [hn, Nat.dvd_sub_iff_left hkn (dvd_refl k)]
  · rw [if_neg hkn, mul_zero]
    by_cases hn : n = 0
    · simp [hn]
    · have hnot : ¬ k ∣ n := fun h => hn (Nat.eq_zero_of_dvd_of_lt h (by omega))
      simp [hn, hnot]

theorem one_sub_mul_lambertLogFactor {k : ℕ} (hk : 0 < k) :
    (1 - PowerSeries.X ^ k) * lambertLogFactor k =
      PowerSeries.C (R := ℤ) (k : ℤ) * PowerSeries.X ^ k := by
  calc
    _ = PowerSeries.C (R := ℤ) (k : ℤ) * PowerSeries.X ^ k *
        ((1 - PowerSeries.X ^ k) * oneSubInv k) := by unfold lambertLogFactor; ring
    _ = _ := by rw [oneSubInv_rightInv hk, mul_one]

theorem powerSeriesEuler_one_sub_X_pow {k : ℕ} (hk : 0 < k) :
    powerSeriesEuler ℤ (1 - PowerSeries.X ^ k) =
      (1 - PowerSeries.X ^ k) * (-lambertLogFactor k) := by
  rw [map_sub, Derivation.map_one_eq_zero, powerSeriesEuler_X_pow, zero_sub,
    mul_neg, one_sub_mul_lambertLogFactor hk]

theorem powerSeriesEuler_oneSubInv {k : ℕ} (hk : 0 < k) :
    powerSeriesEuler ℤ (oneSubInv k) = oneSubInv k * lambertLogFactor k := by
  rw [(powerSeriesEuler ℤ).leibniz_of_mul_eq_one (oneSubInv_leftInv hk),
    powerSeriesEuler_one_sub_X_pow hk]
  simp only [smul_eq_mul]
  calc
    _ = oneSubInv k * lambertLogFactor k *
        (oneSubInv k * (1 - PowerSeries.X ^ k)) := by ring
    _ = _ := by rw [oneSubInv_leftInv hk, mul_one]

/-- The integer series of the canonical sum-of-divisors function sigma_1. -/
noncomputable def sigmaOneSeries : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (ArithmeticFunction.sigma 1 n : ℤ))

theorem coeff_sigmaOneSeries (n : ℕ) :
    PowerSeries.coeff (R := ℤ) n sigmaOneSeries = (ArithmeticFunction.sigma 1 n : ℤ) := by
  rw [sigmaOneSeries, PowerSeries.coeff_mk]

theorem coeff_sum_lambertLogFactor {k n N : ℕ} (hk : 0 < k) (hnN : n ≤ N) :
    (∑ i ∈ Finset.range (N + 1), PowerSeries.coeff (R := ℤ) n (lambertLogFactor (k * (i + 1)))) =
      (k : ℤ) * PowerSeries.coeff (R := ℤ) n
        (MvPowerSeries.subst (fun (_ : Unit) => PowerSeries.X ^ k) sigmaOneSeries) := by
  have hcoef (i : ℕ) := coeff_lambertLogFactor (Nat.mul_pos hk (Nat.succ_pos i)) n
  simp only [hcoef, coeff_subst_X_pow sigmaOneSeries hk, coeff_sigmaOneSeries]
  by_cases hn : n = 0
  · simp [hn]
  simp only [if_neg hn]
  by_cases hkn : k ∣ n
  · rw [if_pos hkn]
    have hm : n / k ≠ 0 := by
      intro hz
      have he := Nat.mul_div_cancel' hkn
      rw [hz, mul_zero] at he
      exact hn he.symm
    have hfilter : (Finset.range (N + 2)).filter (fun d => d ∣ n / k) =
        (n / k).divisors := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
      constructor
      · exact fun h => ⟨h.2, hm⟩
      · intro h
        have hd := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h.1
        have hdiv := Nat.div_le_self n k
        exact ⟨by omega, h.1⟩
    calc
      _ = (k : ℤ) * ∑ i ∈ Finset.range (N + 1),
          if i + 1 ∣ n / k then ((i + 1 : ℕ) : ℤ) else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [← Nat.dvd_div_iff_mul_dvd hkn]
        split_ifs <;> simp [Nat.cast_mul]
      _ = (k : ℤ) * ∑ d ∈ Finset.range (N + 2),
          if d ∣ n / k then (d : ℤ) else 0 := by
        congr 1
        symm
        simpa using Finset.sum_range_succ'
          (fun d => if d ∣ n / k then (d : ℤ) else 0) (N + 1)
      _ = (k : ℤ) * (ArithmeticFunction.sigma 1 (n / k) : ℤ) := by
        rw [← Finset.sum_filter, hfilter, ArithmeticFunction.sigma_one_apply, Nat.cast_sum]
  · rw [if_neg hkn, mul_zero]
    apply Finset.sum_eq_zero
    intro i hi
    have hnot : ¬ k * (i + 1) ∣ n := fun h => hkn ((dvd_mul_right k (i + 1)).trans h)
    exact if_neg hnot

end DirichletL

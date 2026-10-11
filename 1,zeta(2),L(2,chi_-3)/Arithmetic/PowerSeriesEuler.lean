import Arithmetic.PowerSeriesDenominators

/-!
Formal Euler differentiation for the exact q-series in CDT v2, Section 11.1,
equation `haupt` and the beta/gamma definitions (TeX lines 7619-7680).
-/

namespace DirichletL

variable {R : Type*} [CommRing R]

set_option synthInstance.maxHeartbeats 100000 in
/-- The Euler derivation X*d/dX, using Mathlib's formal derivative. -/
noncomputable def powerSeriesEuler (R : Type*) [CommRing R] :
    Derivation R (PowerSeries R) (PowerSeries R) :=
  (PowerSeries.X : PowerSeries R) • PowerSeries.derivative R

theorem powerSeriesEuler_apply (f : PowerSeries R) :
    powerSeriesEuler R f = PowerSeries.X * f.derivativeFun := by
  rw [powerSeriesEuler, Derivation.smul_apply]
  rfl

theorem coeff_powerSeriesEuler (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff (R := R) n (powerSeriesEuler R f) =
      (n : R) * PowerSeries.coeff (R := R) n f := by
  cases n with
  | zero => simp [powerSeriesEuler_apply]
  | succ n =>
    rw [powerSeriesEuler_apply, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_derivativeFun]
    simp [Nat.cast_add, Nat.cast_one, mul_comm]

/-- Euler differentiation commutes with a map of coefficient rings. -/
theorem map_powerSeriesEuler {S : Type*} [CommRing S] (φ : R →+* S)
    (f : PowerSeries R) :
    PowerSeries.map φ (powerSeriesEuler R f) =
      powerSeriesEuler S (PowerSeries.map φ f) := by
  ext n
  simp [PowerSeries.coeff_map, coeff_powerSeriesEuler]

theorem powerSeriesEuler_X_pow (k : ℕ) :
    powerSeriesEuler R (PowerSeries.X ^ k) =
      PowerSeries.C (R := R) (k : R) * PowerSeries.X ^ k := by
  ext n
  rw [coeff_powerSeriesEuler, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  split_ifs with h
  · simp [h]
  · simp

theorem powerSeriesEuler_pow_of_eq {f g : PowerSeries R}
    (hf : powerSeriesEuler R f = f * g) (k : ℕ) :
    powerSeriesEuler R (f ^ k) = f ^ k * (k • g) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Derivation.leibniz, hf, ih]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring

theorem powerSeriesEuler_prod_of_eq {ι : Type*} (s : Finset ι)
    {f g : ι → PowerSeries R}
    (hf : ∀ i ∈ s, powerSeriesEuler R (f i) = f i * g i) :
    powerSeriesEuler R (∏ i ∈ s, f i) =
      (∏ i ∈ s, f i) * ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Derivation.leibniz,
      hf i (Finset.mem_insert_self _ _),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]
    simp only [smul_eq_mul]
    ring

theorem coeff_subst_X_pow (f : PowerSeries R) {k : ℕ} (hk : 0 < k) (n : ℕ) :
    PowerSeries.coeff (R := R) n (MvPowerSeries.subst (fun (_ : Unit) => PowerSeries.X ^ k) f) =
      if k ∣ n then PowerSeries.coeff (R := R) (n / k) f else 0 := by
  have h0 : PowerSeries.constantCoeff (R := R) (PowerSeries.X ^ k) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_X_pow,
      if_neg (by omega)]
  rw [coeff_subst_eq_sum f _ h0]
  simp only [← pow_mul, PowerSeries.coeff_X_pow]
  by_cases hkn : k ∣ n
  · rw [if_pos hkn, Finset.sum_eq_single (n / k)]
    · rw [if_pos (Nat.mul_div_cancel' hkn).symm, mul_one]
    · intro j hj hjn
      have hne : n ≠ k * j := by
        intro h
        apply hjn
        exact mul_left_cancel₀ (Nat.ne_of_gt hk)
          (h.symm.trans (Nat.mul_div_cancel' hkn).symm)
      rw [if_neg hne, mul_zero]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_self n k)))).elim
  · rw [if_neg hkn]
    apply Finset.sum_eq_zero
    intro j hj
    have hne : n ≠ k * j := fun h => hkn ⟨j, h⟩
    rw [if_neg hne, mul_zero]

theorem powerSeriesEuler_two_mk_div_sq (a : ℕ → ℤ) (ha0 : a 0 = 0) :
    powerSeriesEuler ℚ (powerSeriesEuler ℚ
      (PowerSeries.mk (fun n => (a n : ℚ) / (n : ℚ) ^ 2))) =
      PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk a) := by
  ext n
  rw [coeff_powerSeriesEuler, coeff_powerSeriesEuler, PowerSeries.coeff_mk,
    PowerSeries.coeff_map, PowerSeries.coeff_mk]
  simp only [Int.coe_castRingHom]
  by_cases hn : n = 0
  · simp [hn, ha0]
  · field_simp

end DirichletL

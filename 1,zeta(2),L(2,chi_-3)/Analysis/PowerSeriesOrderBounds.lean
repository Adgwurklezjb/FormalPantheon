import Arithmetic.PowerSeriesEuler

/-!
Elementary order operations for the zero estimate in CDT v2,
supplied TeX 2910-2935. These do not assert a quantitative zero estimate.
-/

namespace DirichletL

theorem order_le_powerSeriesEuler {R : Type*} [CommRing R] (f : PowerSeries R) :
    f.order ≤ (powerSeriesEuler R f).order := by
  apply PowerSeries.le_order
  intro n hn
  rw [coeff_powerSeriesEuler, PowerSeries.coeff_of_lt_order n hn, mul_zero]

theorem order_le_iterate_powerSeriesEuler {R : Type*} [CommRing R]
    (f : PowerSeries R) (k : ℕ) :
    f.order ≤ ((powerSeriesEuler R : PowerSeries R → PowerSeries R)^[k] f).order := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (order_le_powerSeriesEuler _)

theorem powerSeries_dvd_iff_order_le {K : Type*} [Field K] (f g : PowerSeries K) :
    f ∣ g ↔ f.order ≤ g.order := by
  constructor
  · rintro ⟨u, rfl⟩
    rw [PowerSeries.order_mul]
    exact le_add_of_nonneg_right bot_le
  · intro h
    by_cases hg : g = 0
    · rw [hg]
      exact dvd_zero _
    have hf : f ≠ 0 := by
      intro hz
      rw [hz, PowerSeries.order_zero, top_le_iff, PowerSeries.order_eq_top] at h
      exact hg h
    rw [← PowerSeries.coe_toNat_order hf] at h
    have hX : (PowerSeries.X : PowerSeries K) ^ f.order.toNat ∣ g := by
      apply PowerSeries.X_pow_dvd_iff.mpr
      intro n hn
      exact PowerSeries.coeff_of_lt_order n ((ENat.coe_lt_coe.mpr hn).trans_le h)
    obtain ⟨a, ha⟩ := hX
    obtain ⟨u, hu⟩ := PowerSeries.isUnit_divided_by_X_pow_order hf
    refine ⟨(↑(u⁻¹) : PowerSeries K) * a, ?_⟩
    calc
      g = PowerSeries.X ^ f.order.toNat * a := ha
      _ = (PowerSeries.X ^ f.order.toNat * (u : PowerSeries K)) *
          ((↑(u⁻¹) : PowerSeries K) * a) := by simp [mul_assoc]
      _ = f * ((↑(u⁻¹) : PowerSeries K) * a) := by
        rw [hu, PowerSeries.X_pow_order_mul_divXPowOrder]

theorem order_coe_polynomial_le_natDegree {K : Type*} [Field K]
    (P : Polynomial K) (hP : P ≠ 0) : (P : PowerSeries K).order ≤ P.natDegree := by
  apply PowerSeries.order_le
  simpa only [Polynomial.coeff_coe, Polynomial.coeff_natDegree] using
    Polynomial.leadingCoeff_ne_zero.mpr hP

theorem nat_le_order_sum_mul {ι R : Type*} [Fintype ι] [CommRing R]
    (a f : ι → PowerSeries R) (N : ℕ) (hf : ∀ i, (N : ℕ∞) ≤ (f i).order) :
    (N : ℕ∞) ≤ (∑ i, a i * f i).order := by
  classical
  apply PowerSeries.nat_le_order
  intro n hn
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact PowerSeries.coeff_mul_of_lt_order ((ENat.coe_lt_coe.mpr hn).trans_le (hf i))

theorem coeff_mul_eq_constantCoeff_mul {R : Type*} [CommRing R]
    (a f : PowerSeries R) (n : ℕ)
    (hf : ∀ k, k < n → PowerSeries.coeff (R := R) k f = 0) :
    PowerSeries.coeff (R := R) n (a * f) =
      PowerSeries.constantCoeff (R := R) a * PowerSeries.coeff (R := R) n f := by
  classical
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, n)]
  · simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · intro p hp hpne
    have hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    have hp0 : p.1 ≠ 0 := by
      intro hz
      apply hpne
      apply Prod.ext
      · exact hz
      · omega
    rw [hf p.2 (by omega), mul_zero]
  · intro hnot
    exact (hnot (by simp)).elim

end DirichletL

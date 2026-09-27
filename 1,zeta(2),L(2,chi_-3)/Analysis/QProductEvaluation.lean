import Analysis.FormalProductEvaluation
import Analysis.QProductAnalytic

/-!
Local complex evaluation of the binomial formal products used in
Lau-Lee-Ono v3 Theorem 4.1.4 and CDT v2 Section 11.1.
-/

namespace DirichletL

theorem hasSum_formalProduct_one_add_C_mul_X_pow {c : ℤ} {e : ℕ → ℕ} {z : ℂ}
    (hc : |c| ≤ 1) (he : ∀ i, i + 1 ≤ e i) (hz : ‖z‖ < 1 / 4) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n (PowerSeries.map (Int.castRingHom ℚ)
      (formalProduct (fun i => 1 + PowerSeries.C (R := ℤ) c * PowerSeries.X ^ e i))) : ℂ) * z ^ n)
      (∏' i, (1 + (c : ℂ) * z ^ e i)) := by
  have hcnorm : ‖(c : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast hc
  apply hasSum_formalProduct_of_hasProd (g := fun i => 1 + (c : ℂ) * z ^ e i)
  · intro i
    rw [add_sub_cancel_left]
    exact dvd_mul_of_dvd_right (pow_dvd_pow PowerSeries.X (he i)) _
  · intro i n
    simp only [map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul_X_pow]
    have hi : e i ≠ 0 := by have := he i; omega
    by_cases hn : n = 0
    · subst n
      simp [Ne.symm hi]
    · by_cases hni : n = e i
      · simpa [hn, hni, hi] using hc
      · simp [hn, hni]
  · exact hz
  · intro i
    convert (hasSum_ite_eq (0 : ℕ) (1 : ℂ)).add
      (hasSum_ite_eq (e i) ((c : ℂ) * z ^ e i)) using 1
    ext n
    simp only [PowerSeries.coeff_map, Int.coe_castRingHom, Rat.cast_intCast,
      map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul_X_pow]
    have hi : e i ≠ 0 := by have := he i; omega
    by_cases hn : n = 0
    · subst n
      simp [Ne.symm hi]
    · by_cases hni : n = e i
      · simp [hn, hni, hi]
      · simp [hn, hni]
  · exact (multipliable_one_add_mul_pow hcnorm he (by linarith)).hasProd

end DirichletL

import Comparator.Statement

/-!
Complex formal factors in CDT v2, supplied TeX 3965-3998 and 4008-4028.
The scalar-series meanings and edge cases are recorded before these proofs
-/

namespace DirichletL

open Filter
open scoped Topology

theorem hasFPowerSeriesAt_ofScalars_iff_eventually_hasSum {c : ℕ → ℂ} {f : ℂ → ℂ} :
    HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ c) 0 ↔
      ∀ᶠ z in 𝓝 0, HasSum (fun n => c n * z ^ n) (f z) := by
  simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add, mul_comm]
    using (hasFPowerSeriesAt_iff (p := FormalMultilinearSeries.ofScalars ℂ c)
      (f := f) (z₀ := 0))

theorem hasSum_complexPowerSeries_mul {p q : PowerSeries ℂ} {z a b : ℂ}
    (hp : HasSum (fun n => PowerSeries.coeff (R := ℂ) n p * z ^ n) a)
    (hq : HasSum (fun n => PowerSeries.coeff (R := ℂ) n q * z ^ n) b) :
    HasSum (fun n => PowerSeries.coeff (R := ℂ) n (p * q) * z ^ n) (a * b) := by
  have hn := summable_norm_sum_mul_antidiagonal_of_summable_norm hp.summable.norm hq.summable.norm
  have hs := hn.of_norm.hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    hp.summable.norm hq.summable.norm, hp.tsum_eq, hq.tsum_eq] at hs
  convert hs using 1
  ext n
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [← Finset.mem_antidiagonal.mp hij, pow_add]
  ring

theorem hasFPowerSeriesAt_complexPowerSeries_mul {p q : PowerSeries ℂ} {f g : ℂ → ℂ}
    (hf : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n p)) 0)
    (hg : HasFPowerSeriesAt g
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n q)) 0) :
    HasFPowerSeriesAt (fun z => f z * g z)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n (p * q))) 0 := by
  apply hasFPowerSeriesAt_ofScalars_iff_eventually_hasSum.mpr
  filter_upwards [hasFPowerSeriesAt_ofScalars_iff_eventually_hasSum.mp hf,
    hasFPowerSeriesAt_ofScalars_iff_eventually_hasSum.mp hg] with z hfz hgz
  exact hasSum_complexPowerSeries_mul hfz hgz

theorem hasFPowerSeriesAt_complexPolynomial (P : Polynomial ℂ) :
    HasFPowerSeriesAt (fun z => P.eval z)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff (R := ℂ) n (P : PowerSeries ℂ))) 0 := by
  apply hasFPowerSeriesAt_ofScalars_iff_eventually_hasSum.mpr
  apply Filter.Eventually.of_forall
  intro z
  simp only [Polynomial.coeff_coe, Polynomial.eval_eq_sum, Polynomial.sum]
  exact hasSum_sum_of_ne_finset_zero (fun n hn => by
    rw [Polynomial.not_mem_support_iff.mp hn, zero_mul])

theorem hasFPowerSeriesAt_complexPowerSeries_pow {p : PowerSeries ℂ} {f : ℂ → ℂ}
    (hf : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n p)) 0) (k : ℕ) :
    HasFPowerSeriesAt (fun z => f z ^ k)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n (p ^ k))) 0 := by
  induction k with
  | zero =>
    simpa only [pow_zero, Polynomial.coe_one, Polynomial.eval_one] using
      hasFPowerSeriesAt_complexPolynomial (1 : Polynomial ℂ)
  | succ k ih =>
    simpa only [pow_succ] using hasFPowerSeriesAt_complexPowerSeries_mul ih hf

theorem hasFPowerSeriesAt_complexPowerSeries_X_pow_mul {p : PowerSeries ℂ} {f : ℂ → ℂ}
    (hf : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n p)) 0) (k : ℕ) :
    HasFPowerSeriesAt (fun z => z ^ k * f z)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff (R := ℂ) n (PowerSeries.X ^ k * p))) 0 := by
  have hx : HasFPowerSeriesAt (fun z : ℂ => z ^ k)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff (R := ℂ) n (PowerSeries.X ^ k))) 0 := by
    have h := hasFPowerSeriesAt_complexPolynomial ((Polynomial.X : Polynomial ℂ) ^ k)
    simpa only [Polynomial.coe_pow, Polynomial.coe_X, Polynomial.eval_pow,
      Polynomial.eval_X] using h
  exact hasFPowerSeriesAt_complexPowerSeries_mul hx hf

end DirichletL

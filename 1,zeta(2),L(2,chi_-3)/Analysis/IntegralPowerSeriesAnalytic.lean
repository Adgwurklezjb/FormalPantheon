import Analysis.PowerSeriesCompositionAnalytic

/-!
Analytic ring operations for integer power series mapped to rational coefficients.
These support the case-C and numerator identities of Zagier (2009), Sections 5-6.
-/

namespace DirichletL

theorem hasFPowerSeriesAt_int_mul {p r : PowerSeries ℤ} {f g : ℂ → ℂ}
    (hf : HasFPowerSeriesAt f (complexSeries (PowerSeries.map (Int.castRingHom ℚ) p)) 0)
    (hg : HasFPowerSeriesAt g (complexSeries (PowerSeries.map (Int.castRingHom ℚ) r)) 0) :
    HasFPowerSeriesAt (fun q => f q * g q)
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) (p * r))) 0 := by
  simpa only [map_mul] using hasFPowerSeriesAt_powerSeries_mul hf hg

theorem hasFPowerSeriesAt_int_pow {p : PowerSeries ℤ} {f : ℂ → ℂ}
    (hf : HasFPowerSeriesAt f (complexSeries (PowerSeries.map (Int.castRingHom ℚ) p)) 0)
    (n : ℕ) :
    HasFPowerSeriesAt (fun q => f q ^ n)
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) (p ^ n))) 0 := by
  simpa only [map_pow] using hasFPowerSeriesAt_powerSeries_pow hf n

theorem hasFPowerSeriesAt_int_sub {p r : PowerSeries ℤ} {f g : ℂ → ℂ}
    (hf : HasFPowerSeriesAt f (complexSeries (PowerSeries.map (Int.castRingHom ℚ) p)) 0)
    (hg : HasFPowerSeriesAt g (complexSeries (PowerSeries.map (Int.castRingHom ℚ) r)) 0) :
    HasFPowerSeriesAt (fun q => f q - g q)
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) (p - r))) 0 := by
  convert hf.sub hg using 1
  ext n v
  simp [complexSeries, FormalMultilinearSeries.ofScalars]

theorem hasFPowerSeriesAt_int_add {p r : PowerSeries ℤ} {f g : ℂ → ℂ}
    (hf : HasFPowerSeriesAt f (complexSeries (PowerSeries.map (Int.castRingHom ℚ) p)) 0)
    (hg : HasFPowerSeriesAt g (complexSeries (PowerSeries.map (Int.castRingHom ℚ) r)) 0) :
    HasFPowerSeriesAt (fun q => f q + g q)
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) (p + r))) 0 := by
  convert hf.add hg using 1
  ext n v
  simp [complexSeries, FormalMultilinearSeries.ofScalars]

theorem hasFPowerSeriesAt_int_const (a : ℤ) :
    HasFPowerSeriesAt (fun _ : ℂ => (a : ℂ))
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) (a : PowerSeries ℤ))) 0 := by
  have hC : (a : PowerSeries ℤ) = PowerSeries.C (R := ℤ) a :=
    (map_intCast (PowerSeries.C (R := ℤ)) a).symm
  rw [hC, PowerSeries.map_C]
  apply hasFPowerSeriesAt_of_eventually_hasSum
  apply Filter.Eventually.of_forall
  intro q
  convert (hasSum_ite_eq (0 : ℕ) (a : ℂ)) using 1
  ext n
  by_cases hn : n = 0
  · subst n
    simp [PowerSeries.coeff_C]
  · simp only [PowerSeries.coeff_C, if_neg hn, Rat.cast_zero, zero_mul]

end DirichletL

import Analysis.ComplexPowerSeriesComposition
import Analysis.MeromorphicPolynomialClearing

/-!
The actual cleared factors in CDT v2, supplied TeX 4008-4028 (`G pull`).
Meanings and the order of polynomial and exponent choices precede these
-/

namespace DirichletL

theorem hasFPowerSeriesAt_cleared_composed_factor {p q : PowerSeries ℂ} {f φ : ℂ → ℂ}
    (H : Polynomial ℂ)
    (hf : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n p)) 0)
    (hφ : HasFPowerSeriesAt φ
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n q)) 0)
    (hq0 : PowerSeries.constantCoeff (R := ℂ) q = 0) (k : ℕ) :
    HasFPowerSeriesAt (fun z => H.eval z * φ z ^ k * f (φ z))
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n
        ((H : PowerSeries ℂ) * (q ^ k * MvPowerSeries.subst (fun _ : Unit => q) p)))) 0 := by
  have hcomp := hasFPowerSeriesAt_complexPowerSeries_subst hf hφ hq0
  have hpow := hasFPowerSeriesAt_complexPowerSeries_pow hφ k
  simpa only [Function.comp_apply, mul_assoc] using
    hasFPowerSeriesAt_complexPowerSeries_mul (hasFPowerSeriesAt_complexPolynomial H)
      (hasFPowerSeriesAt_complexPowerSeries_mul hpow hcomp)

theorem analyticOnNhd_cleared_composed_factor {f φ : ℂ → ℂ} (H : Polynomial ℂ)
    {K : Set ℂ} (hφ : AnalyticOnNhd ℂ φ K)
    (hclear : AnalyticOnNhd ℂ (fun z => H.eval z * f (φ z)) K) (k : ℕ) :
    AnalyticOnNhd ℂ (fun z => H.eval z * φ z ^ k * f (φ z)) K := by
  intro z hz
  simpa only [mul_assoc, mul_left_comm] using ((hφ z hz).fun_pow k).mul (hclear z hz)

theorem exists_common_polynomial_clear_compact_powers {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ℂ → ℂ) (φ : κ → ℂ → ℂ) {K : Set ℂ} (hK : IsCompact K)
    (hφ : ∀ j, AnalyticOnNhd ℂ (φ j) K)
    (hf : ∀ i j, MeromorphicOn (fun z => f i (φ j z)) K)
    (h0 : ∀ i j, AnalyticAt ℂ (fun z => f i (φ j z)) 0) :
    ∃ H : Polynomial ℂ, H.eval 0 = 1 ∧
      ∀ i j (k : ℕ), AnalyticOnNhd ℂ (fun z => H.eval z * φ j z ^ k * f i (φ j z)) K := by
  obtain ⟨H, hH0, hH⟩ := exists_common_polynomial_clear_compact
    (fun ij : ι × κ => fun z => f ij.1 (φ ij.2 z)) hK
    (fun ij => hf ij.1 ij.2) (fun ij => h0 ij.1 ij.2)
  exact ⟨H, hH0, fun i j k => analyticOnNhd_cleared_composed_factor H (hφ j) (hH (i, j)) k⟩

end DirichletL

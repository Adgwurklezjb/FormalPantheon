import Mathlib

/-!
Canonical scalar expansions for CDT v2 TeX 3505-3526 and 4008-4021.
-/

namespace DirichletL

theorem exists_powerSeries_of_analyticAt_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ φ : PowerSeries ℂ,
      HasFPowerSeriesAt f
        (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n φ)) 0 ∧
      PowerSeries.constantCoeff (R := ℂ) φ = f 0 ∧ PowerSeries.coeff (R := ℂ) 1 φ = deriv f 0 := by
  obtain ⟨p, hp⟩ := hf
  let φ : PowerSeries ℂ := PowerSeries.mk p.coeff
  have hseries : FormalMultilinearSeries.ofScalars ℂ
      (fun n => PowerSeries.coeff (R := ℂ) n φ) = p := by
    funext n
    apply ContinuousMultilinearMap.ext
    intro z
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      FormalMultilinearSeries.coeff_ofScalars, φ, PowerSeries.coeff_mk]
  refine ⟨φ, ?_, ?_, ?_⟩
  · rw [hseries]
    exact hp
  · simpa only [φ, PowerSeries.constantCoeff_mk, FormalMultilinearSeries.coeff]
      using hp.coeff_zero (fun _ => 1)
  · simpa only [φ, PowerSeries.coeff_mk, FormalMultilinearSeries.coeff] using hp.deriv.symm

end DirichletL

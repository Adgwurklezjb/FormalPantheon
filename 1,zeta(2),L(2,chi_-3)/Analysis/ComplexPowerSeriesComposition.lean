import Analysis.ComplexPowerSeriesEvaluation
import Analysis.PowerSeriesCompositionAnalytic

/-!
Complex formal substitution for CDT v2, supplied TeX 4008-4028.
The native scalar composition and coefficient meanings are recorded before
-/

namespace DirichletL

theorem coeff_comp_ofScalars {p : PowerSeries ℂ}
    (hp : 0 < (FormalMultilinearSeries.ofScalars ℂ
      (fun n => PowerSeries.coeff (R := ℂ) n p)).radius)
    (hp0 : PowerSeries.constantCoeff (R := ℂ) p = 0)
    (q : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (q.comp (FormalMultilinearSeries.ofScalars ℂ
      (fun n => PowerSeries.coeff (R := ℂ) n p))).coeff n =
        ∑ k ∈ Finset.range (n + 1), q.coeff k * PowerSeries.coeff (R := ℂ) n (p ^ k) := by
  let S := FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n p)
  have hf := (S.hasFPowerSeriesOnBall hp).hasFPowerSeriesAt
  have hf0 : S.sum 0 = 0 := by
    have h := hf.coeff_zero (fun _ => 1)
    simpa [S, FormalMultilinearSeries.ofScalars,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hp0] using h.symm
  rw [coeff_comp_eq_sum_monomial]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  have hm := hasFPowerSeriesAt_powerSeries_pow hasFPowerSeriesAt_complexSeries_X k
  have hm' : HasFPowerSeriesAt (fun z : ℂ => z ^ k)
      (complexSeries (PowerSeries.X ^ k)) (S.sum 0) := by
    simpa only [hf0, id_eq] using hm
  have he := (hm'.comp hf).eq_formalMultilinearSeries
    (hasFPowerSeriesAt_complexPowerSeries_pow hf k)
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using
    congrArg (fun s => s.coeff n) he

theorem ofScalars_complexPowerSeries_subst {p q : PowerSeries ℂ}
    (hq : 0 < (FormalMultilinearSeries.ofScalars ℂ
      (fun n => PowerSeries.coeff (R := ℂ) n q)).radius)
    (hq0 : PowerSeries.constantCoeff (R := ℂ) q = 0) :
    FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff (R := ℂ) n (MvPowerSeries.subst (fun _ : Unit => q) p)) =
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n p)).comp
        (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n q)) := by
  ext n v
  rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.apply_eq_prod_smul_coeff]
  congr 1
  rw [FormalMultilinearSeries.coeff_ofScalars, coeff_subst_eq_sum p q hq0,
    coeff_comp_ofScalars hq hq0]
  simp only [FormalMultilinearSeries.coeff_ofScalars]

theorem hasFPowerSeriesAt_complexPowerSeries_subst {p q : PowerSeries ℂ} {f g : ℂ → ℂ}
    (hf : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n p)) 0)
    (hg : HasFPowerSeriesAt g
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n q)) 0)
    (hq0 : PowerSeries.constantCoeff (R := ℂ) q = 0) :
    HasFPowerSeriesAt (f ∘ g)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff (R := ℂ) n (MvPowerSeries.subst (fun _ : Unit => q) p))) 0 := by
  have hg0 : g 0 = 0 := by
    have h := hg.coeff_zero (fun _ => 1)
    simpa [FormalMultilinearSeries.ofScalars,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hq0] using h.symm
  rw [ofScalars_complexPowerSeries_subst hg.radius_pos hq0]
  exact (hg0.symm ▸ hf).comp hg

end DirichletL

import Analysis.ClearedComposedFactors

/-!
Meromorphic representatives of composed germs in CDT v2 TeX 3523
and 4011. Meanings and exceptional cases precede these bodies in
-/

namespace DirichletL

open scoped Topology

theorem hasFPowerSeriesAt_cleared_continued_factor {p q : PowerSeries ℂ}
    {f ψ P : ℂ → ℂ} (H : Polynomial ℂ)
    (hf : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n p)) 0)
    (hψ : HasFPowerSeriesAt ψ
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n q)) 0)
    (hq0 : PowerSeries.constantCoeff (R := ℂ) q = 0)
    (hP : P =ᶠ[𝓝 (0 : ℂ)] fun z => f (ψ z)) (k : ℕ) :
    HasFPowerSeriesAt (fun z => H.eval z * ψ z ^ k * P z)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n
        ((H : PowerSeries ℂ) * (q ^ k * MvPowerSeries.subst (fun _ : Unit => q) p)))) 0 := by
  apply (hasFPowerSeriesAt_cleared_composed_factor H hf hψ hq0 k).congr
  filter_upwards [hP] with z hz
  rw [hz]

theorem analyticOnNhd_cleared_continued_factor {ψ P : ℂ → ℂ} (H : Polynomial ℂ)
    {K : Set ℂ} (hψ : AnalyticOnNhd ℂ ψ K)
    (hclear : AnalyticOnNhd ℂ (fun z => H.eval z * P z) K) (k : ℕ) :
    AnalyticOnNhd ℂ (fun z => H.eval z * ψ z ^ k * P z) K := by
  intro z hz
  simpa only [mul_assoc, mul_left_comm] using ((hψ z hz).fun_pow k).mul (hclear z hz)

theorem exists_common_polynomial_clear_continued_compact {ι κ : Type*}
    [Fintype ι] [Fintype κ] (F : ι → ℂ → ℂ) (ψ : κ → ℂ → ℂ)
    (P : ι → κ → ℂ → ℂ) {K : Set ℂ} (hK : IsCompact K)
    (hF : ∀ i, AnalyticAt ℂ (F i) 0) (hψ : ∀ q, AnalyticAt ℂ (ψ q) 0)
    (hψ0 : ∀ q, ψ q 0 = 0)
    (hP : ∀ i q, P i q =ᶠ[𝓝 (0 : ℂ)] fun z => F i (ψ q z))
    (hmero : ∀ i q, MeromorphicOn (P i q) K) :
    ∃ H : Polynomial ℂ, H.eval 0 = 1 ∧
      ∀ i q, AnalyticOnNhd ℂ (fun z => H.eval z * P i q z) K := by
  have hlocal (iq : ι × κ) : AnalyticAt ℂ (P iq.1 iq.2) 0 := by
    have hcomp : AnalyticAt ℂ (fun z => F iq.1 (ψ iq.2 z)) 0 :=
      (hF iq.1).comp_of_eq' (hψ iq.2) (hψ0 iq.2)
    exact hcomp.congr (hP iq.1 iq.2).symm
  obtain ⟨H, hH0, hH⟩ := exists_common_polynomial_clear_compact
    (fun iq : ι × κ => P iq.1 iq.2) hK (fun iq => hmero iq.1 iq.2) hlocal
  exact ⟨H, hH0, fun i q => hH (i, q)⟩

end DirichletL

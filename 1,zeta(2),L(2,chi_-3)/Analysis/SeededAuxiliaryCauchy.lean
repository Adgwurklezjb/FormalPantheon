import Analysis.SeededAuxiliaryExpression
import Analysis.ContinuedComposedFactors
import Analysis.TorusPolynomialCoefficient

/-!
The literal auxiliary coefficient integral in CDT v2, supplied TeX 4092-4137.
Meanings, finite indices, and the normalization precede these proofs in

The continuation interface is recorded before this revision in
-/

namespace DirichletL

open MeasureTheory
open scoped Classical Topology

attribute [local instance] fact_two_pi_pos

theorem coeff_seeded_auxiliaryFormalSeries_eq_torusIntegral {m : ℕ}
    (f : Fin m → PowerSeries ℚ) (F : Fin m → ℂ → ℂ) (h D : ℕ) (ε : ℝ)
    (t : ↥(auxiliaryFreeIndices m h D ε) → ℤ) (π : Equiv.Perm (Fin (m * h)))
    (φ : Fin (m * h) → PowerSeries ℂ) (ψ : Fin (m * h) → ℂ → ℂ)
    (P : Fin m → Fin (m * h) → ℂ → ℂ)
    (H : Polynomial ℂ) (W : MvPolynomial (Fin (m * h)) ℂ)
    (hf : ∀ i, HasFPowerSeriesAt (F i) (complexSeries (f i)) 0)
    (hψ : ∀ j, HasFPowerSeriesAt (ψ j)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n (φ j))) 0)
    (hφ : ∀ j, PowerSeries.constantCoeff (R := ℂ) (φ j) = 0)
    (hP : ∀ i j, P i j =ᶠ[𝓝 (0 : ℂ)] fun z => F i (ψ j z))
    (hdψ : ∀ j, AnalyticOnNhd ℂ (ψ j) (Metric.closedBall 0 1))
    (hH : ∀ i j, AnalyticOnNhd ℂ (fun z => H.eval z * P i j z) (Metric.closedBall 0 1))
    (n : Fin (m * h) →₀ ℕ) :
    MvPowerSeries.coeff (R := ℂ) n ((W : MvPowerSeries (Fin (m * h)) ℂ) *
      ((∏ j, powerSeriesInVariable ℂ j (H : PowerSeries ℂ)) *
        MvPowerSeries.subst (fun j => powerSeriesInVariable ℂ j (φ j))
          (MvPowerSeries.map (σ := (Fin (m * h))) (algebraMap ℚ ℂ)
            (MvPowerSeries.subst
              (fun j => (MvPowerSeries.X (π.symm j) : MvPowerSeries (Fin (m * h)) ℚ))
              (auxiliaryFormalSeries f h D ε t))))) =
      ∫ z : Fin (m * h) → AddCircle (2 * Real.pi),
        (MvPolynomial.eval (fun j => fourier 1 (z j)) W *
          (∑ v, (t v : ℂ) * ∏ j, H.eval (fourier 1 (z j)) *
            ψ j (fourier 1 (z j)) ^ (v.val.2 (π j)).val *
              P (v.val.1 (π j)) j (fourier 1 (z j)))) *
          ∏ j, fourier (-(n j : ℤ)) (z j)
        ∂Measure.pi (fun _ : Fin (m * h) => AddCircle.haarAddCircle) := by
  rw [seeded_auxiliaryFormalSeries_eq_sum f h D ε t π φ (H : PowerSeries ℂ) hφ]
  refine coeff_polynomial_mul_sum_separate_eq_torusIntegral W (fun v => (t v : ℂ))
    (fun v j => (H : PowerSeries ℂ) *
      (φ j ^ (v.val.2 (π j)).val * MvPowerSeries.subst (fun _ : Unit => φ j)
        (PowerSeries.map (algebraMap ℚ ℂ) (f (v.val.1 (π j))))))
    (fun v j z => H.eval z * ψ j z ^ (v.val.2 (π j)).val * P (v.val.1 (π j)) j z)
    ?_ ?_ n
  · intro v j
    have hfi : HasFPowerSeriesAt (F (v.val.1 (π j)))
        (FormalMultilinearSeries.ofScalars ℂ (fun k => PowerSeries.coeff (R := ℂ) k
          (PowerSeries.map (algebraMap ℚ ℂ) (f (v.val.1 (π j)))))) 0 := by
      simpa only [complexSeries, PowerSeries.coeff_map] using hf (v.val.1 (π j))
    exact hasFPowerSeriesAt_cleared_continued_factor H hfi (hψ j) (hφ j)
      (hP (v.val.1 (π j)) j) (v.val.2 (π j)).val
  · intro v j
    exact (analyticOnNhd_cleared_continued_factor H (hdψ j)
      (hH (v.val.1 (π j)) j) (v.val.2 (π j)).val).differentiableOn

theorem norm_coeff_seeded_auxiliaryFormalSeries_le_of_bound {m : ℕ}
    (f : Fin m → PowerSeries ℚ) (F : Fin m → ℂ → ℂ) (h D : ℕ) (ε : ℝ)
    (t : ↥(auxiliaryFreeIndices m h D ε) → ℤ) (π : Equiv.Perm (Fin (m * h)))
    (φ : Fin (m * h) → PowerSeries ℂ) (ψ : Fin (m * h) → ℂ → ℂ)
    (P : Fin m → Fin (m * h) → ℂ → ℂ)
    (H : Polynomial ℂ) (W : MvPolynomial (Fin (m * h)) ℂ)
    (hf : ∀ i, HasFPowerSeriesAt (F i) (complexSeries (f i)) 0)
    (hψ : ∀ j, HasFPowerSeriesAt (ψ j)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n (φ j))) 0)
    (hφ : ∀ j, PowerSeries.constantCoeff (R := ℂ) (φ j) = 0)
    (hP : ∀ i j, P i j =ᶠ[𝓝 (0 : ℂ)] fun z => F i (ψ j z))
    (hdψ : ∀ j, AnalyticOnNhd ℂ (ψ j) (Metric.closedBall 0 1))
    (hH : ∀ i j, AnalyticOnNhd ℂ (fun z => H.eval z * P i j z) (Metric.closedBall 0 1))
    (n : Fin (m * h) →₀ ℕ) (C : ℝ)
    (hC : ∀ z : Fin (m * h) → AddCircle (2 * Real.pi),
      ‖MvPolynomial.eval (fun j => fourier 1 (z j)) W *
        (∑ v, (t v : ℂ) * ∏ j, H.eval (fourier 1 (z j)) *
          ψ j (fourier 1 (z j)) ^ (v.val.2 (π j)).val *
            P (v.val.1 (π j)) j (fourier 1 (z j)))‖ ≤ C) :
    ‖MvPowerSeries.coeff (R := ℂ) n ((W : MvPowerSeries (Fin (m * h)) ℂ) *
      ((∏ j, powerSeriesInVariable ℂ j (H : PowerSeries ℂ)) *
        MvPowerSeries.subst (fun j => powerSeriesInVariable ℂ j (φ j))
          (MvPowerSeries.map (σ := (Fin (m * h))) (algebraMap ℚ ℂ)
            (MvPowerSeries.subst
              (fun j => (MvPowerSeries.X (π.symm j) : MvPowerSeries (Fin (m * h)) ℚ))
              (auxiliaryFormalSeries f h D ε t)))))‖ ≤ C := by
  rw [coeff_seeded_auxiliaryFormalSeries_eq_torusIntegral f F h D ε t π φ ψ P H W
    hf hψ hφ hP hdψ hH n]
  have hb : ∀ᵐ z : Fin (m * h) → AddCircle (2 * Real.pi)
      ∂Measure.pi (fun _ : Fin (m * h) => AddCircle.haarAddCircle),
      ‖(MvPolynomial.eval (fun j => fourier 1 (z j)) W *
        (∑ v, (t v : ℂ) * ∏ j, H.eval (fourier 1 (z j)) *
          ψ j (fourier 1 (z j)) ^ (v.val.2 (π j)).val *
            P (v.val.1 (π j)) j (fourier 1 (z j)))) *
        ∏ j, fourier (-(n j : ℤ)) (z j)‖ ≤ C :=
    Filter.Eventually.of_forall (fun z => by
      simpa only [norm_mul, norm_prod_fourier, mul_one] using hC z)
  simpa using norm_integral_le_of_norm_le_const hb

end DirichletL

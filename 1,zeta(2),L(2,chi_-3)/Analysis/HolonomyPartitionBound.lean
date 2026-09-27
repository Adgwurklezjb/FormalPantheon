import Analysis.HolonomyPartitionCoefficient
import Analysis.PartitionHolonomyLimits

/-!
Conditional closed-disc specialization of CDT v2's signed fine bound,
TeX 3503-3541. Meanings precede this body in

The continuation interface is recorded before this revision in
-/

namespace DirichletL

open scoped Classical Topology

theorem cdt_partition_holonomy_bound (a₀ b₀ c₀ : ℤ)
    (hrel : (a₀ : ℝ) + (b₀ : ℝ) * (lTwoChiMinusThree / 2) +
      (c₀ : ℝ) * (zetaTwo / 4) = 0) (hne : ¬(a₀ = 0 ∧ b₀ = 0 ∧ c₀ = 0))
    {s : ℕ} (hs : 0 < s) (v : Fin (s + 1) → ℝ) (hv : StrictMono v)
    (hv0 : v 0 = 0) (hv1 : v (Fin.last s) = 1)
    (φ : Fin s → PowerSeries ℂ) (ψ : Fin s → ℂ → ℂ)
    (P : Fin 14 → Fin s → ℂ → ℂ) (H : Polynomial ℂ)
    (hψ : ∀ q, HasFPowerSeriesAt (ψ q)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n (φ q))) 0)
    (hφ : ∀ q, PowerSeries.constantCoeff (R := ℂ) (φ q) = 0)
    (hP : ∀ i q, P i q =ᶠ[𝓝 (0 : ℂ)] fun z =>
      cdtHolonomyFamily a₀ b₀ c₀ i (ψ q z))
    (hderiv : ∀ q, deriv (ψ q) 0 ≠ 0)
    (hdψ : ∀ q, AnalyticOnNhd ℂ (ψ q) (Metric.closedBall 0 1))
    (hH0 : H.eval 0 = 1)
    (hH : ∀ i q, AnalyticOnNhd ℂ
      (fun z => H.eval z * P i q z) (Metric.closedBall 0 1))
    (hcircle : ∀ q (z : ℂ), ‖z‖ = 1 → ψ q z ≠ 0) :
    14 * (∑ q, (v q.succ ^ 2 - v q.castSucc ^ 2) * Real.log ‖deriv (ψ q) 0‖) ≤
      14 * (16603 / 3920 : ℝ) + ∑ q : Fin s, ∑ r : Fin s,
        (v q.succ - v q.castSucc) * (v r.succ - v r.castSucc) *
        pairwiseMaxIntegral (circleLogProfile (ψ q)) (circleLogProfile (ψ r)) := by
  have hderivEq (q : Fin s) : deriv (ψ q) 0 = PowerSeries.coeff (R := ℂ) 1 (φ q) := by
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one]
      using (hψ q).deriv
  have hφ1 (q : Fin s) : PowerSeries.coeff (R := ℂ) 1 (φ q) ≠ 0 := by
    rw [← hderivEq q]
    exact hderiv q
  let K : ℝ := ∑ q, |Real.log ‖PowerSeries.coeff (R := ℂ) 1 (φ q)‖|
  have hK0 : 0 ≤ K := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hK (q : Fin s) : |Real.log ‖PowerSeries.coeff (R := ℂ) 1 (φ q)‖| ≤ K :=
    Finset.single_le_sum (f := fun r => |Real.log ‖PowerSeries.coeff (R := ℂ) 1 (φ r)‖|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ q)
  let W : ℝ := ∑ q, (v q.succ ^ 2 - v q.castSucc ^ 2) *
    Real.log ‖PowerSeries.coeff (R := ℂ) 1 (φ q)‖
  let J : ℝ := ∑ q : Fin s, ∑ r : Fin s,
    (v q.succ - v q.castSucc) * (v r.succ - v r.castSucc) *
    pairwiseMaxIntegral (circleLogProfile (ψ q)) (circleLogProfile (ψ r))
  obtain ⟨B, hB, C, hbounds⟩ := exists_cdt_partition_coefficient_normalized_bound
    a₀ b₀ c₀ hrel hne hs v hv hv0 hv1 φ ψ P H hψ hφ hP hφ1 hdψ hH0 hH hcircle hK
  simp_rw [hderivEq]
  change 14 * W ≤ 14 * (16603 / 3920 : ℝ) + J
  apply partition_holonomy_le_of_errors hB hK0
  intro ε hε η hη ξ hξ ζ hζ
  obtain ⟨c, _hc, hboundsξ⟩ := hbounds ξ hξ
  obtain ⟨ε', δ, hε', hε'ε, hε'1, hδ, hδε', _hδ14, hscalar⟩ :=
    hboundsξ ε hε η hη
  have hlim := partition_holonomy_le_of_eventually (hscalar ζ hζ)
  let T : ℝ := 14 * ((16603 / 3920 : ℝ) + η) + J + 4 * ξ + 2 * ζ
  have hsmall := partition_holonomy_remove_delta (W := W) (T := T) hB hK0
    hε'.le hε'ε hδ.le hδε'.le (hδε'.le.trans hε'1) (by
      dsimp only [T]
      linarith only [hlim])
  dsimp only [T] at hsmall
  linarith only [hsmall]

end DirichletL

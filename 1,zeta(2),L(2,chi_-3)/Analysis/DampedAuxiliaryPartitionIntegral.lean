import Analysis.DampedAuxiliaryPartitionGrid
import Analysis.UniformBlockGridIntegral

/-!
The signed integral exponent for the literal coefficient, CDT v2 supplied
TeX 3998-4028 and 4130-4228. Meanings and parameter order precede this body

The continuation interface is recorded before this revision in
-/

namespace DirichletL

open Filter
open scoped Classical Topology

theorem exists_damped_auxiliary_partition_integral_bound {s m : ℕ} (hs : 0 < s)
    (a : Fin (s + 1) → ℝ) (ha : StrictMono a)
    (ha0 : a 0 = 0) (ha1 : a (Fin.last s) = 1)
    (f : Fin m → PowerSeries ℚ) (F : Fin m → ℂ → ℂ)
    (φ : Fin s → PowerSeries ℂ) (ψ : Fin s → ℂ → ℂ)
    (P : Fin m → Fin s → ℂ → ℂ) (H : Polynomial ℂ)
    (hf : ∀ i, HasFPowerSeriesAt (F i) (complexSeries (f i)) 0)
    (hψ : ∀ q, HasFPowerSeriesAt (ψ q)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff (R := ℂ) n (φ q))) 0)
    (hφ : ∀ q, PowerSeries.constantCoeff (R := ℂ) (φ q) = 0)
    (hP : ∀ i q, P i q =ᶠ[𝓝 (0 : ℂ)] fun z => F i (ψ q z))
    (hdψ : ∀ q, AnalyticOnNhd ℂ (ψ q) (Metric.closedBall 0 1))
    (hH : ∀ i q, AnalyticOnNhd ℂ (fun z => H.eval z * P i q z)
      (Metric.closedBall 0 1))
    (hne : ∀ q (z : ℂ), ‖z‖ = 1 → ψ q z ≠ 0) :
    let J : ℝ := ∑ q : Fin s, ∑ r : Fin s,
      (a q.succ - a q.castSucc) * (a r.succ - a r.castSucc) *
      pairwiseMaxIntegral (circleLogProfile (ψ q)) (circleLogProfile (ψ r))
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, ∀ ξ : ℝ, 0 < ξ →
      ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ h : ℕ, N ≤ m * h →
      ∃ b : Fin (m * h) → Fin s,
        (∀ j q, b j = q ↔ a q.castSucc * (m * h : ℕ) ≤ (j.val : ℝ) + 1 ∧
          ((j.val : ℝ) + 1 < a q.succ * (m * h : ℕ) ∨ q.succ = Fin.last s)) ∧
        (∀ q, |((Finset.univ.filter (fun j => b j = q)).card : ℝ) -
          (a q.succ - a q.castSucc) * (m * h : ℕ)| ≤ 1) ∧
        ∀ (D : ℕ) (ε : ℝ), 0 < D → 0 ≤ ε →
        ∀ (t : ↥(auxiliaryFreeIndices m h D ε) → ℤ) (π : Equiv.Perm (Fin (m * h)))
          (S : ℝ), (∀ v, ‖(t v : ℂ)‖ ≤ Real.exp S) →
        ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ (2 * B / c) * D / (m * h : ℕ) + 2 ∧
          blockVandermondePolynomial (R := ℂ) b M ≠ 0 ∧
          ∀ n : Fin (m * h) →₀ ℕ,
          ‖MvPowerSeries.coeff (R := ℂ) n
            ((blockVandermondePolynomial (R := ℂ) b M : MvPowerSeries (Fin (m * h)) ℂ) *
              ((∏ j, powerSeriesInVariable ℂ j (H : PowerSeries ℂ)) *
                MvPowerSeries.subst (fun j => powerSeriesInVariable ℂ j (φ (b j)))
                  (MvPowerSeries.map (σ := (Fin (m * h))) (algebraMap ℚ ℂ)
                    (MvPowerSeries.subst
                      (fun j => (MvPowerSeries.X (π.symm j) : MvPowerSeries (Fin (m * h)) ℚ))
                      (auxiliaryFormalSeries f h D ε t)))))‖ ≤
            Real.exp (Real.log ((auxiliaryFreeIndices m h D ε).card : ℝ) +
              S + (m * h : ℕ) * C +
              (D : ℝ) * (m * h : ℕ) * (J / 2 + 2 * ξ + ε * B) +
              (M : ℝ) * (m * h : ℕ) * Real.log (m * h : ℕ)) := by
  let p (q : Fin s) : ℝ := a q.succ - a q.castSucc
  let J : ℝ := ∑ q, ∑ r, p q * p r *
    pairwiseMaxIntegral (circleLogProfile (ψ q)) (circleLogProfile (ψ r))
  have hp (q : Fin s) : 0 < p q := sub_pos.mpr (ha (Fin.castSucc_lt_succ q))
  have hpsum : ∑ q, p q = 1 := by
    have hfirst := Fin.sum_univ_succ a
    have hlast := Fin.sum_univ_castSucc a
    simp only [ha0, ha1, zero_add] at hfirst hlast
    dsimp only [p]
    rw [Finset.sum_sub_distrib]
    linarith only [hfirst, hlast]
  have hcont (q : Fin s) :
      ContinuousOn (circleLogProfile (ψ q)) (Set.Icc (0 : ℝ) 1) :=
    (continuous_circleLogProfile (hdψ q).continuousOn (hne q)).continuousOn
  obtain ⟨B, hB, C, hprevious⟩ := exists_damped_auxiliary_partition_grid_bound hs a ha ha0 ha1
    f F φ ψ P H hf hψ hφ hP hdψ hH hne
  refine ⟨B, hB, C, ?_⟩
  intro ξ hξ
  obtain ⟨c, hc, Np, hNp⟩ := hprevious ξ hξ
  obtain ⟨Ni, hNi⟩ := eventually_atTop.1
    (eventually_abs_two_mul_sortedGridSum_block_sub_integral_le
      (fun q => circleLogProfile (ψ q)) hcont p hp hpsum (show 0 < 2 * ξ by positivity))
  refine ⟨c, hc, max Np (max Ni 1), ?_⟩
  intro h hd
  have hdp : Np ≤ m * h := (le_max_left Np (max Ni 1)).trans hd
  have hdi : Ni ≤ m * h := by omega
  have hdpos : 0 < m * h := by omega
  have hdR : (0 : ℝ) < (m * h : ℕ) := by exact_mod_cast hdpos
  obtain ⟨b, hb, hcard, hcoefficients⟩ := hNp h hdp
  have hint := hNi (m * h) hdi b hcard
  change |2 * sortedGridSum (blockGridValues b (fun q => circleLogProfile (ψ q))) /
    (m * h : ℕ) - J| ≤ 2 * ξ at hint
  have hfrac : 2 * sortedGridSum (blockGridValues b (fun q => circleLogProfile (ψ q))) /
      (m * h : ℕ) ≤ J + 2 * ξ := by
    have hbound := (abs_le.mp hint).2
    linarith only [hbound]
  have hsort : sortedGridSum (blockGridValues b (fun q => circleLogProfile (ψ q))) ≤
      (m * h : ℕ) * (J / 2 + ξ) := by
    have hscaled := (div_le_iff₀ hdR).mp hfrac
    nlinarith only [hscaled]
  refine ⟨b, hb, hcard, ?_⟩
  intro D ε hD hε t π S ht
  have hDR : (0 : ℝ) ≤ D := by exact_mod_cast hD.le
  have hgrowth : blockGridGrowth b (fun q => circleLogProfile (ψ q)) D ξ ε B ≤
      (D : ℝ) * (m * h : ℕ) * (J / 2 + 2 * ξ + ε * B) := by
    calc
      _ = D * sortedGridSum (blockGridValues b (fun q => circleLogProfile (ψ q))) +
          (D : ℝ) * (m * h : ℕ) * (ξ + ε * B) := rfl
      _ ≤ D * ((m * h : ℕ) * (J / 2 + ξ)) + (D : ℝ) * (m * h : ℕ) * (ξ + ε * B) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hsort hDR) _
      _ = _ := by ring
  obtain ⟨M, hM, hMbound, hW, hcoeff⟩ := hcoefficients D ε hD hε t π S ht
  refine ⟨M, hM, hMbound, hW, ?_⟩
  intro n
  apply (hcoeff n).trans
  apply Real.exp_le_exp.mpr
  linarith only [hgrowth]

end DirichletL

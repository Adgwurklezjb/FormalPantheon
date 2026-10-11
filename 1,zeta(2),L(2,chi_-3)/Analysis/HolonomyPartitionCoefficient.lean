import Analysis.HolonomyAuxiliarySeeding
import Analysis.DampedAuxiliaryPartitionIntegral
import Analysis.PartitionCoefficientComparison
import Analysis.PartitionHolonomyAlgebra
import Analysis.AuxiliarySizeBounds

/-!
One actual coefficient in CDT v2 TeX 3998-4028 and 4188-4229.

The continuation interface is recorded before this revision in
-/

namespace DirichletL

open Filter
open scoped Classical Topology

theorem exists_cdt_partition_coefficient_normalized_bound (a₀ b₀ c₀ : ℤ)
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
    (hφ1 : ∀ q, PowerSeries.coeff (R := ℂ) 1 (φ q) ≠ 0)
    (hdψ : ∀ q, AnalyticOnNhd ℂ (ψ q) (Metric.closedBall 0 1))
    (hH0 : H.eval 0 = 1)
    (hH : ∀ i q, AnalyticOnNhd ℂ
      (fun z => H.eval z * P i q z) (Metric.closedBall 0 1))
    (hcircle : ∀ q (z : ℂ), ‖z‖ = 1 → ψ q z ≠ 0)
    {K : ℝ} (hK : ∀ q, |Real.log ‖PowerSeries.coeff (R := ℂ) 1 (φ q)‖| ≤ K) :
    let W : ℝ := ∑ q, (v q.succ ^ 2 - v q.castSucc ^ 2) *
      Real.log ‖PowerSeries.coeff (R := ℂ) 1 (φ q)‖
    let J : ℝ := ∑ q : Fin s, ∑ r : Fin s,
      (v q.succ - v q.castSucc) * (v r.succ - v r.castSucc) *
      pairwiseMaxIntegral (circleLogProfile (ψ q)) (circleLogProfile (ψ r))
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, ∀ ξ : ℝ, 0 < ξ → ∃ c : ℝ, 0 < c ∧
      ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η →
      ∃ ε' δ : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ 1 ∧ 0 < δ ∧ δ < ε' ∧ δ < 14 ∧
      ∀ ζ : ℝ, 0 < ζ → ∀ᶠ h : ℕ in atTop, ∀ᶠ D : ℕ in atTop,
        (14 + δ) * W ≤ 14 * ((16603 / 3920 : ℝ) + η) + J +
          4 * ξ + 2 * ε' * B + 2 * ζ +
          (2 * (Real.log 14 + Real.log D) + 2 * C + 4 * Real.log (14 * h : ℕ)) / D +
          (4 * B / c) * Real.log (14 * h : ℕ) / (14 * h : ℕ) +
          (14 + δ) * (2 * ε' * K + 3 * (s : ℝ) * K / (14 * h : ℕ)) := by
  let W : ℝ := ∑ q, (v q.succ ^ 2 - v q.castSucc ^ 2) *
    Real.log ‖PowerSeries.coeff (R := ℂ) 1 (φ q)‖
  let J : ℝ := ∑ q : Fin s, ∑ r : Fin s,
    (v q.succ - v q.castSucc) * (v r.succ - v r.castSucc) *
    pairwiseMaxIntegral (circleLogProfile (ψ q)) (circleLogProfile (ψ r))
  have hrelQ : ((a₀ : ℚ) : ℝ) + ((b₀ : ℚ) : ℝ) * (lTwoChiMinusThree / 2) +
      ((c₀ : ℚ) : ℝ) * (zetaTwo / 4) = 0 := by
    simpa only [Rat.cast_intCast] using hrel
  obtain ⟨B, hB, C, hupper⟩ := exists_damped_auxiliary_partition_integral_bound
    hs v hv hv0 hv1 (cdtHolonomySeries a₀ b₀ c₀) (cdtHolonomyFamily a₀ b₀ c₀)
    φ ψ P H (hasFPowerSeriesAt_cdtHolonomyFamily a₀ b₀ c₀ hrelQ)
    hψ hφ hP hdψ hH hcircle
  refine ⟨B, hB, C, ?_⟩
  intro ξ hξ
  obtain ⟨c, hc, N, hN⟩ := hupper ξ hξ
  refine ⟨c, hc, ?_⟩
  intro ε hε η hη
  obtain ⟨ε', δ, hε', hε'ε, hε'1, hδ, hδε', hδ14, hselect⟩ :=
    exists_cdtAuxiliaryFormalSeries_seeded_vandermonde_coefficient a₀ b₀ c₀ hrel hne hε hη
  refine ⟨ε', δ, hε', hε'ε, hε'1, hδ, hδε', hδ14, ?_⟩
  intro ζ hζ
  filter_upwards [hselect ζ hζ, eventually_gt_atTop (0 : ℕ), eventually_ge_atTop N]
    with h hselecth hh hNh
  let d : ℕ := 14 * h
  have hd : 0 < d := by dsimp only [d]; omega
  have hNd : N ≤ 14 * h := by omega
  obtain ⟨b, hb, _hcard, hcoefficients⟩ := hN h hNd
  let HH : MvPowerSeries (Fin d) ℂ := ∏ j, powerSeriesInVariable ℂ j (H : PowerSeries ℂ)
  have hHH0 : MvPowerSeries.constantCoeff (σ := (Fin d)) (R := ℂ) HH = 1 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    change MvPowerSeries.coeff (R := ℂ) 0
      (∏ j : Fin d, powerSeriesInVariable ℂ j (H : PowerSeries ℂ)) = 1
    rw [coeff_prod_powerSeriesInVariable]
    simp only [Finsupp.zero_apply, Polynomial.coeff_coe,
      Polynomial.coeff_zero_eq_eval_zero, hH0, Finset.prod_const_one]
  filter_upwards [hselecth, eventually_gt_atTop (0 : ℕ)] with D hselectD hD
  let R : ℝ := (14 + δ) * D
  have hR : 0 < R := by dsimp only [R]; positivity
  let L : ℕ := ⌈R⌉₊
  have hRL : R ≤ (L : ℝ) := Nat.le_ceil R
  have hLR : (L : ℝ) ≤ R + 1 := (Nat.ceil_lt_add_one hR.le).le
  obtain ⟨t, n, σ, ht, hsize, _hF, hn, _hmin, hmono, hnL, hdis,
    _hlarge, hlower, hseed⟩ := hselectD L hRL hLR
  let S : ℝ := ζ * (d : ℝ) * D
  obtain ⟨M, _hMpos, hM, _hW, hcoeff⟩ := hcoefficients D ε' hD hε'.le t σ S
    (fun i => by rw [Complex.norm_intCast]; exact hsize i)
  let β : ℚ := MvPowerSeries.coeff (R := ℚ) n
    (auxiliaryFormalSeries (cdtHolonomySeries a₀ b₀ c₀) h D ε' t)
  let p : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => n (σ j))
  let q : Fin d →₀ ℕ := ∑ ij ∈ blockVandermondePairs b, M • Finsupp.single ij.2 (1 : ℕ)
  let A : MvPowerSeries (Fin d) ℂ := MvPowerSeries.map (σ := (Fin d)) (algebraMap ℚ ℂ)
    (MvPowerSeries.subst (fun j => (MvPowerSeries.X (σ.symm j) : MvPowerSeries (Fin d) ℚ))
      (auxiliaryFormalSeries (cdtHolonomySeries a₀ b₀ c₀) h D ε' t))
  let γ : ℂ := MvPowerSeries.coeff (R := ℂ) (p + q)
    ((blockVandermondePolynomial (R := ℂ) b M : MvPowerSeries (Fin d) ℂ) *
      (HH * MvPowerSeries.subst (fun j => powerSeriesInVariable ℂ j (φ (b j))) A))
  have hγ : γ = (β : ℂ) * ∏ j, PowerSeries.coeff (R := ℂ) 1 (φ (b j)) ^ n (σ j) := by
    have hseed' := (hseed HH (fun j => φ (b j)) hHH0 (fun j => hφ (b j))
      (fun j => hφ1 (b j)) (blockVandermondePairs b)
      (fun ij hij => ((mem_blockVandermondePairs b ij).mp hij).1) M).1
    dsimp only [γ]
    rw [coe_blockVandermondePolynomial]
    simpa only [p, Finsupp.coe_equivFunOnFinite_symm] using hseed'
  let V : ℝ := Real.log ((auxiliaryFreeIndices 14 h D ε').card : ℝ) + S + (d : ℝ) * C +
    (D : ℝ) * d * (J / 2 + 2 * ξ + ε' * B) + (M : ℝ) * d * Real.log d
  have hγbound : ‖γ‖ ≤ Real.exp V := hcoeff (p + q)
  have hcomp := partition_weighted_log_norm_le_of_coeff_bounds hs hd hR
    (fun j => n j) σ hmono hdis hnL hLR v hv.monotone hv0 hv1 b hb β hn
    (fun q => PowerSeries.coeff (R := ℂ) 1 (φ q)) hφ1 γ hγ
    (98 * (h : ℝ) * D * ((16603 / 3920 : ℝ) + η)) V hlower hγbound hK
  have hQpos : 0 < (auxiliaryFreeIndices 14 h D ε').card := by
    apply Finset.card_pos.mpr
    by_contra hQempty
    apply ht
    funext i
    exact False.elim (hQempty ⟨i.val, i.property⟩)
  have hQ := log_card_auxiliaryFreeIndices_le (by decide : 0 < 14) hD hQpos
  have hnormalized : W ≤
      2 * (7 * (d : ℝ) * D * ((16603 / 3920 : ℝ) + η) +
        Real.log ((auxiliaryFreeIndices 14 h D ε').card : ℝ) + ζ * d * D + d * C +
        (D : ℝ) * d * (J / 2 + 2 * ξ + ε' * B) + (M : ℝ) * d * Real.log d) /
          ((14 + δ) * D * d) + 2 * ε' * K + 3 * (s : ℝ) * K / d := by
    convert hcomp using 1
    dsimp only [V, S, R, d]
    push_cast
    ring
  exact partition_holonomy_normalized_bound hd hD (by linarith only [hδ]) hc.ne'
    hQ hM hnormalized

end DirichletL

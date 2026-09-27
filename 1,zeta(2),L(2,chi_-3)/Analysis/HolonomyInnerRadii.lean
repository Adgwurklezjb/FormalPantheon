import Analysis.HolonomyMeromorphicBound
import Analysis.AnalyticBoundaryRadii

/-!
The common inner-radius reduction of CDT v2 TeX 4150-4153, with its
actual-family use at 8325-8333. Meanings precede this body in

The continuation interface is recorded before this revision in
-/

namespace DirichletL

open Filter
open scoped Topology

theorem cdt_partition_holonomy_bound_eventually_inner_radius (a₀ b₀ c₀ : ℤ)
    (hrel : (a₀ : ℝ) + (b₀ : ℝ) * (lTwoChiMinusThree / 2) +
      (c₀ : ℝ) * (zetaTwo / 4) = 0) (hne : ¬(a₀ = 0 ∧ b₀ = 0 ∧ c₀ = 0))
    {s : ℕ} (hs : 0 < s) (v : Fin (s + 1) → ℝ) (hv : StrictMono v)
    (hv0 : v 0 = 0) (hv1 : v (Fin.last s) = 1) (ψ : Fin s → ℂ → ℂ)
    (P : Fin 14 → Fin s → ℂ → ℂ)
    (hψ0 : ∀ q, ψ q 0 = 0)
    (hP : ∀ i q, P i q =ᶠ[𝓝 (0 : ℂ)] fun z =>
      cdtHolonomyFamily a₀ b₀ c₀ i (ψ q z))
    (hderiv : ∀ q, deriv (ψ q) 0 ≠ 0)
    (hdψ : ∀ q, AnalyticOnNhd ℂ (ψ q) (Metric.closedBall 0 1))
    (hmero : ∀ i q, MeromorphicOn (P i q) (Metric.ball 0 1)) :
    ∀ᶠ r : ℝ in 𝓝[<] 1,
      14 * (∑ q, (v q.succ ^ 2 - v q.castSucc ^ 2) *
        Real.log ‖(r : ℂ) * deriv (ψ q) 0‖) ≤
        14 * (16603 / 3920 : ℝ) + ∑ q : Fin s, ∑ t : Fin s,
          (v q.succ - v q.castSucc) * (v t.succ - v t.castSucc) *
          pairwiseMaxIntegral (circleLogProfile (fun z => ψ q ((r : ℂ) * z)))
            (circleLogProfile (fun z => ψ t ((r : ℂ) * z))) := by
  have hpos : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [eventually_family_sphere_ne_zero ψ hdψ hderiv,
    hpos, self_mem_nhdsWithin] with r hcircle hr hr1
  exact cdt_partition_holonomy_bound_inner_radius a₀ b₀ c₀ hrel hne hs v hv hv0 hv1
    ψ P hψ0 hP hderiv hdψ hmero hr hr1 hcircle

end DirichletL

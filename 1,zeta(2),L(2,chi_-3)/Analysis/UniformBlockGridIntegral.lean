import Analysis.PairwiseBlockGrid
import Analysis.ConsecutiveBlockBounds

/-!
The uniform signed integral limit in CDT v2, supplied TeX 3503-3540
and 4150-4228. Meanings and threshold order precede this body in
-/

namespace DirichletL

open Filter

theorem eventually_abs_two_mul_sortedGridSum_block_sub_integral_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : κ → ℝ → ℝ) (hf : ∀ q, ContinuousOn (f q) (Set.Icc (0 : ℝ) 1))
    (p : κ → ℝ) (hp : ∀ q, 0 < p q) (hpsum : ∑ q, p q = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : ℕ in atTop, ∀ b : Fin d → κ,
      (∀ q, |((Finset.univ.filter (fun i => b i = q)).card : ℝ) - p q * d| ≤ 1) →
      |2 * sortedGridSum (blockGridValues b f) / d -
        ∑ q, ∑ r, p q * p r * pairwiseMaxIntegral (f q) (f r)| ≤ ε := by
  classical
  have hc : ContinuousOn (fun u q => f q u) (Set.Icc (0 : ℝ) 1) := continuousOn_pi.mpr hf
  obtain ⟨U, hU⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  let B : ℝ := max 0 U
  have hB : 0 ≤ B := le_max_left _ _
  have hfB (q : κ) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) : |f q u| ≤ B :=
    (norm_le_pi_norm (fun q => f q u) q).trans ((hU u hu).trans (le_max_right _ _))
  obtain ⟨η, hη, hgrid⟩ :=
    exists_uniform_pairwiseMaxGridAverage_tolerance f hf (show 0 < ε / 4 by positivity)
  obtain ⟨w, hw, hwp⟩ := Pi.exists_forall_pos_add_lt hp
  let ρ : ℝ := w / 2
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hmeshEvent : ∀ᶠ d : ℕ in atTop, (1 / ρ) / (d : ℝ) < η :=
    Filter.Tendsto.eventually_lt_const hη (tendsto_const_div_atTop_nhds_zero_nat (1 / ρ))
  have herrorEvent : ∀ᶠ d : ℕ in atTop,
      (1 + 2 * (Fintype.card κ : ℝ)) * B / (d : ℝ) < ε / 2 :=
    Filter.Tendsto.eventually_lt_const (by positivity)
      (tendsto_const_div_atTop_nhds_zero_nat ((1 + 2 * (Fintype.card κ : ℝ)) * B))
  filter_upwards [eventually_ge_atTop ⌈2 / w⌉₊, hmeshEvent, herrorEvent]
    with d hdcut hdmesh hderror
  intro b hcard
  have hcut : 2 / w ≤ (d : ℝ) := (Nat.le_ceil (2 / w)).trans (by exact_mod_cast hdcut)
  have hdR : (0 : ℝ) < d := lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 / w) hcut
  have hd : 0 < d := by exact_mod_cast hdR
  have hsizeR (q : κ) : ρ * d ≤ ((Finset.univ.filter (fun i => b i = q)).card : ℝ) :=
    consecutiveBlockSize_ge_half_width hw
      (by simpa only [zero_add] using (hwp q).le) (hcard q) hcut
  have hsize (q : κ) : 0 < (Finset.univ.filter (fun i => b i = q)).card := by
    have h := (mul_pos hρ hdR).trans_le (hsizeR q)
    exact_mod_cast h
  have hmesh (q : κ) : 1 / ((Finset.univ.filter (fun i => b i = q)).card : ℝ) ≤ η := by
    calc
      _ ≤ 1 / (ρ * (d : ℝ)) := one_div_le_one_div_of_le (mul_pos hρ hdR) (hsizeR q)
      _ = (1 / ρ) / (d : ℝ) := by ring
      _ ≤ η := hdmesh.le
  have h := abs_two_mul_sortedGridSum_block_sub_integral_le b f hd hsize p
    (fun q => (hp q).le) hpsum hcard hB hfB
    (fun q r => hgrid q r _ _ (hsize q) (hsize r) (hmesh q) (hmesh r))
  exact h.trans (by linarith only [hderror])

end DirichletL

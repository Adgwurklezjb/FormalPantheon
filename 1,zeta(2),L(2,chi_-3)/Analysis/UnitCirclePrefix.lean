import Comparator.Statement

/-!
Continuous bounds for interval counts in the circle discrepancy argument
of CDT v2, supplied TeX 4054-4067, and published UDC Lemma 2.5.9.
The geometric meanings and endpoint checks precede these proofs in
-/

namespace DirichletL

open MeasureTheory Metric
open scoped Classical

local instance fact_one_pos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem coe_mem_unitCircle_closedBall_half {θ u : ℝ} (hθ : 0 ≤ θ) (hθu : θ ≤ u) :
    (θ : AddCircle (1 : ℝ)) ∈ closedBall ((u / 2 : ℝ) : AddCircle (1 : ℝ)) (u / 2) := by
  rw [mem_closedBall, dist_eq_norm, ← QuotientAddGroup.mk_sub]
  apply (QuotientAddGroup.norm_mk_le_norm :
    ‖((θ - u / 2 : ℝ) : AddCircle (1 : ℝ))‖ ≤ ‖θ - u / 2‖).trans
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem lt_of_coe_mem_unitCircle_ball_half {θ u : ℝ} (hθ : θ ≤ 1)
    (hb : (θ : AddCircle (1 : ℝ)) ∈ ball ((u / 2 : ℝ) : AddCircle (1 : ℝ)) (u / 2)) :
    θ < u := by
  rw [mem_ball, dist_eq_norm, ← QuotientAddGroup.mk_sub, AddCircle.norm_eq] at hb
  simp only [inv_one, one_mul, mul_one] at hb
  by_contra h
  by_cases hn : round (θ - u / 2) ≤ 0
  · have hnR : (round (θ - u / 2) : ℝ) ≤ 0 := by exact_mod_cast hn
    have hle := le_abs_self (θ - u / 2 - (round (θ - u / 2) : ℝ))
    linarith
  · have hn' : 1 ≤ round (θ - u / 2) := by omega
    have hnR : (1 : ℝ) ≤ round (θ - u / 2) := by exact_mod_cast hn'
    have hle := neg_le_abs (θ - u / 2 - (round (θ - u / 2) : ℝ))
    linarith

theorem unitCircle_haar_real_closedBall (x : AddCircle (1 : ℝ)) (r : ℝ) :
    AddCircle.haarAddCircle.real (closedBall x r) = max 0 (min 1 (2 * r)) := by
  have hμ : (volume : Measure (AddCircle (1 : ℝ))) = AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  change (AddCircle.haarAddCircle (closedBall x r)).toReal = _
  rw [← hμ, AddCircle.volume_closedBall, ENNReal.toReal_ofReal', max_comm]

theorem exists_unitCircle_ball_cutoff (x : AddCircle (1 : ℝ)) {r R : ℝ} (hrR : r < R) :
    ∃ f : C(AddCircle (1 : ℝ), ℝ), (∀ y, f y ∈ Set.Icc (0 : ℝ) 1) ∧
      Set.EqOn f 1 (closedBall x r) ∧ Set.EqOn f 0 (ball x R)ᶜ ∧
      max 0 (min 1 (2 * r)) ≤ ∫ y, f y ∂AddCircle.haarAddCircle ∧
      (∫ y, f y ∂AddCircle.haarAddCircle) ≤ max 0 (min 1 (2 * R)) := by
  have hdis : Disjoint (ball x R)ᶜ (closedBall x r) := by
    apply Set.disjoint_left.mpr
    intro y hy hclosed
    exact hy (closedBall_subset_ball hrR hclosed)
  obtain ⟨f, hf0, hf1, hfr⟩ := exists_continuous_zero_one_of_isClosed
    isOpen_ball.isClosed_compl isClosed_closedBall hdis
  have hfi : Integrable f AddCircle.haarAddCircle := by
    simpa only [integrableOn_univ] using
      f.continuous.continuousOn.integrableOn_compact
        (μ := AddCircle.haarAddCircle) isCompact_univ
  have hIi (t : ℝ) : Integrable ((closedBall x t).indicator (fun _ => (1 : ℝ)))
      AddCircle.haarAddCircle :=
    (integrable_const (1 : ℝ)).indicator measurableSet_closedBall
  refine ⟨f, hfr, hf1, hf0, ?_, ?_⟩
  · have h := integral_mono (hIi r) hfi (fun y => by
      by_cases hy : y ∈ closedBall x r
      · simp [hy, hf1 hy]
      · simpa [hy] using (hfr y).1)
    rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_one,
      unitCircle_haar_real_closedBall] at h
    exact h
  · have h := integral_mono hfi (hIi R) (fun y => by
      by_cases hy : y ∈ closedBall x R
      · simpa [hy] using (hfr y).2
      · have hn : y ∉ ball x R := fun h => hy (ball_subset_closedBall h)
        simp [hy, hf0 hn])
    rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_one,
      unitCircle_haar_real_closedBall] at h
    exact h

theorem exists_continuous_unitCircle_prefix_bounds {u η : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hη : 0 < η) :
    ∃ f g : C(AddCircle (1 : ℝ), ℝ),
      (∀ y, f y ∈ Set.Icc (0 : ℝ) 1 ∧ g y ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ θ ∈ Set.Icc (0 : ℝ) 1,
        f (θ : AddCircle (1 : ℝ)) ≤ (if θ < u then 1 else 0) ∧
        (if θ ≤ u then 1 else 0) ≤ g (θ : AddCircle (1 : ℝ))) ∧
      u - η ≤ (∫ y, f y ∂AddCircle.haarAddCircle) ∧
      (∫ y, g y ∂AddCircle.haarAddCircle) ≤ u + η := by
  obtain ⟨f, hf, _, hf0, hfint, _⟩ := exists_unitCircle_ball_cutoff
    ((u / 2 : ℝ) : AddCircle (1 : ℝ)) (r := (u - η) / 2) (R := u / 2) (by linarith)
  obtain ⟨g, hg, hg1, _, _, hgint⟩ := exists_unitCircle_ball_cutoff
    ((u / 2 : ℝ) : AddCircle (1 : ℝ)) (r := u / 2) (R := (u + η) / 2) (by linarith)
  refine ⟨f, g, fun y => ⟨hf y, hg y⟩, ?_, ?_, ?_⟩
  · intro θ hθ
    constructor
    · by_cases h : θ < u
      · simpa only [if_pos h] using (hf (θ : AddCircle (1 : ℝ))).2
      · have hn : (θ : AddCircle (1 : ℝ)) ∉
            ball ((u / 2 : ℝ) : AddCircle (1 : ℝ)) (u / 2) :=
          fun hb => h (lt_of_coe_mem_unitCircle_ball_half hθ.2 hb)
        simp [h, hf0 hn]
    · by_cases h : θ ≤ u
      · simp [h, hg1 (coe_mem_unitCircle_closedBall_half hθ.1 h)]
      · simpa only [if_neg h] using (hg (θ : AddCircle (1 : ℝ))).1
  · rw [show 2 * ((u - η) / 2) = u - η by ring,
      min_eq_right (by linarith [hu.2] : u - η ≤ 1)] at hfint
    exact (le_max_right _ _).trans hfint
  · rw [show 2 * ((u + η) / 2) = u + η by ring] at hgint
    exact hgint.trans (max_le (by linarith [hu.1]) (min_le_right _ _))

end DirichletL

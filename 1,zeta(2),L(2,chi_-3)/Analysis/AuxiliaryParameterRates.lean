import Arithmetic.BalancedCardinalityAsymptotic

/-!
Exact parameter rates used in the finite auxiliary count of CDT v2,
supplied TeX 3950-4004. Dimension tends to infinity before the
cutoff limit is applied at each fixed dimension.
-/

namespace DirichletL

open Filter Set
open scoped Topology

theorem exists_pos_nat_mesh {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, 0 < q ∧ 1 / (q : ℝ) ≤ ε / 8 := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by positivity : (0 : ℝ) < ε / 8)
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  exact le_of_lt (by simpa only [Nat.cast_add, Nat.cast_one] using hn)

theorem eventually_uniform_lattice_population_mesh {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ D : ℕ in atTop, 0 < D ∧ ∀ L : ℕ, a * D ≤ L → 1 / (L : ℝ) ≤ ε / 8 := by
  have hlim : Tendsto (fun D : ℕ => 1 / (a * D)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, mul_inv_rev, zero_mul] using
      tendsto_inverse_atTop_nhds_zero_nat.mul_const a⁻¹
  filter_upwards [hlim.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 8)),
    eventually_gt_atTop (0 : ℕ)] with D hD hh
  refine ⟨hh, fun L hL => ?_⟩
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hh
  exact (one_div_le_one_div_of_le (mul_pos ha hDR) hL).trans hD.le

theorem exists_auxiliary_delta {m ε κ : ℝ} (hm : 0 < m) (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ δ < m ∧ (m + δ) * Real.exp (-κ) < m - δ := by
  let r := Real.exp (-κ)
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hcap : 0 < m * (1 - r) / (1 + r) :=
    div_pos (mul_pos hm (sub_pos.mpr hr1)) (by positivity)
  obtain ⟨δ, hδ, hδcap⟩ := exists_between
    (lt_min hε (lt_min hm hcap))
  have hδε := hδcap.trans_le (min_le_left _ _)
  have hδm := hδcap.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδr := hδcap.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hmul := (lt_div_iff₀ (by positivity : (0 : ℝ) < 1 + r)).mp hδr
  refine ⟨δ, hδ, hδε, hδm, ?_⟩
  change (m + δ) * r < m - δ
  nlinarith

theorem eventually_pow_lt_card_balancedSpeciesIndices {m : ℕ} (hm : 1 < m)
    {b : ℝ} (hb : 0 < b) (hbm : b < m) :
    ∀ᶠ h : ℕ in atTop, b ^ (m * h) < ((balancedSpeciesIndices m h).card : ℝ) := by
  have hlog : 0 < Real.log (m : ℝ) - Real.log b :=
    sub_pos.mpr (Real.log_lt_log hb hbm)
  filter_upwards [eventually_log_card_balancedSpeciesIndices_gt hm hlog] with h hh
  have hB : 0 < ((balancedSpeciesIndices m h).card : ℝ) := by
    exact_mod_cast card_balancedSpeciesIndices_pos m h
  apply (Real.log_lt_log_iff (pow_pos hb _) hB).mp
  rw [Real.log_pow]
  nlinarith

theorem tendsto_geometric_sum_div_one_sub {m : ℕ} (hm : 0 < m) {r s t C : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hs : 0 ≤ s) (hs1 : s < 1)
    (ht : 0 ≤ t) (ht1 : t < 1) :
    Tendsto (fun h : ℕ => (r ^ (m * h) + C * s ^ (m * h)) /
      (1 - C * t ^ (m * h))) atTop (𝓝 (0 : ℝ)) := by
  have hlim {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
      Tendsto (fun h : ℕ => u ^ (m * h)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [pow_mul] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (pow_nonneg hu m) (pow_lt_one₀ hu hu1 hm.ne')
  simpa only [mul_zero, add_zero, sub_zero, zero_div] using
    ((hlim hr hr1).add ((hlim hs hs1).const_mul C)).div
      (tendsto_const_nhds.sub ((hlim ht ht1).const_mul C)) (by simp)

theorem tendsto_scaled_cube_majorant (a b E : ℝ) (d : ℕ) :
    Tendsto (fun D : ℕ => (a + 1 / (D : ℝ)) ^ d + E * (b + 1 / (D : ℝ)) ^ d)
      atTop (𝓝 (a ^ d + E * b ^ d)) := by
  simpa only [add_zero] using
    ((tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat).pow d).add
      (((tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat).pow d).const_mul E)

theorem nat_dirichlet_ratio_le_of_mul_le {M N : ℕ} (hN : 0 < N) {θ : ℝ}
    (hθ1 : θ < 1) (hMN : (M : ℝ) ≤ θ * N) :
    M < N ∧ (M : ℝ) / (N - M : ℕ) ≤ θ / (1 - θ) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hltR : (M : ℝ) < N := by nlinarith
  have hlt : M < N := by exact_mod_cast hltR
  refine ⟨hlt, ?_⟩
  rw [Nat.cast_sub hlt.le]
  apply (div_le_div_iff₀ (sub_pos.mpr hltR) (sub_pos.mpr hθ1)).mpr
  nlinarith

end DirichletL

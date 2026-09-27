import Arithmetic.BalancedCardinalityBound

/-!
The asymptotically full species count in CDT v2, supplied TeX 3806-3823.
The exact finite count and its polynomial loss imply a normalized
logarithmic limit for each fixed number of species greater than one.
-/

namespace DirichletL

open Filter Set
open scoped Topology

theorem log_card_balancedSpeciesIndices_le (m h : ℕ) :
    Real.log ((balancedSpeciesIndices m h).card : ℝ) ≤ (m * h : ℕ) * Real.log m := by
  have hpos : 0 < ((balancedSpeciesIndices m h).card : ℝ) := by
    exact_mod_cast card_balancedSpeciesIndices_pos m h
  have hle : ((balancedSpeciesIndices m h).card : ℝ) ≤ (m : ℝ) ^ (m * h) := by
    exact_mod_cast card_balancedSpeciesIndices_le_pow m h
  simpa only [Real.log_pow] using Real.log_le_log hpos hle

theorem log_card_balancedSpeciesIndices_lower {m h : ℕ} (hm : 1 < m) (hh : 0 < h) :
    (m * h : ℕ) * Real.log (m : ℝ) - (m - 1 : ℕ) * Real.log (m * h + m - 1 : ℕ) <
      Real.log ((balancedSpeciesIndices m h).card : ℝ) := by
  have hpos : 0 < ((balancedSpeciesIndices m h).card : ℝ) := by
    exact_mod_cast card_balancedSpeciesIndices_pos m h
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hb : 0 < (m * h + m - 1 : ℕ) := by omega
  have hbR : 0 < ((m * h + m - 1 : ℕ) : ℝ) := by exact_mod_cast hb
  have hlt : (m : ℝ) ^ (m * h) < ((balancedSpeciesIndices m h).card : ℝ) *
      ((m * h + m - 1 : ℕ) : ℝ) ^ (m - 1) := by
    exact_mod_cast pow_lt_card_balancedSpeciesIndices_mul_pow hm hh
  have hl := Real.log_lt_log (pow_pos hmR _) hlt
  rw [Real.log_mul hpos.ne' (pow_pos hbR _).ne'] at hl
  simp only [Real.log_pow] at hl
  linarith

theorem tendsto_log_nat_affine_div (a b : ℕ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => Real.log (a * n + b : ℕ) / (a * n : ℕ)) atTop (𝓝 (0 : ℝ)) := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hN : Tendsto (fun n : ℕ => (a : ℝ) * n) atTop atTop :=
    Filter.Tendsto.const_mul_atTop haR tendsto_natCast_atTop_atTop
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hN
  have hd := (Real.tendsto_log_comp_add_sub_log (b : ℝ)).comp hN
  have ht := hl.add (hd.div_atTop hN)
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [] with n
  dsimp only [Function.comp_def, id_eq]
  push_cast
  ring

theorem tendsto_log_card_balancedSpeciesIndices_div {m : ℕ} (hm : 1 < m) :
    Tendsto (fun h : ℕ => Real.log ((balancedSpeciesIndices m h).card : ℝ) / (m * h : ℕ))
      atTop (𝓝 (Real.log m)) := by
  let e : ℕ → ℝ := fun h => (m - 1 : ℕ) *
    (Real.log (m * h + (m - 1) : ℕ) / (m * h : ℕ))
  have he : Tendsto e atTop (𝓝 (0 : ℝ)) := by
    simpa only [e, mul_zero] using
      (tendsto_log_nat_affine_div m (m - 1) (by omega)).const_mul ((m - 1 : ℕ) : ℝ)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [he.eventually (Iio_mem_nhds hε), eventually_gt_atTop (0 : ℕ)]
    with h heh hh
  have hN : 0 < ((m * h : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < m) hh
  have hu : Real.log ((balancedSpeciesIndices m h).card : ℝ) / (m * h : ℕ) ≤ Real.log m :=
    (div_le_iff₀ hN).2 (by simpa only [mul_comm] using log_card_balancedSpeciesIndices_le m h)
  have hl₀ := log_card_balancedSpeciesIndices_lower hm hh
  have hsub : m * h + m - 1 = m * h + (m - 1) := by omega
  rw [hsub] at hl₀
  have hl := div_lt_div_of_pos_right hl₀ hN
  have heq : ((m * h : ℕ) * Real.log (m : ℝ) -
      (m - 1 : ℕ) * Real.log (m * h + (m - 1) : ℕ)) / (m * h : ℕ) = Real.log m - e h := by
    dsimp only [e]
    field_simp [hN.ne']
  rw [heq] at hl
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hu)]
  change e h < ε at heh
  linarith

theorem eventually_log_card_balancedSpeciesIndices_gt {m : ℕ} (hm : 1 < m)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℕ in atTop, (m * h : ℕ) * (Real.log (m : ℝ) - ε) <
      Real.log ((balancedSpeciesIndices m h).card : ℝ) := by
  have hnear := (tendsto_log_card_balancedSpeciesIndices_div hm).eventually
    (Ioi_mem_nhds (by linarith : Real.log (m : ℝ) - ε < Real.log (m : ℝ)))
  filter_upwards [hnear, eventually_gt_atTop (0 : ℕ)] with h hrate hh
  have hN : 0 < ((m * h : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < m) hh
  have hmul := (lt_div_iff₀ hN).mp hrate
  simpa only [mul_comm] using hmul

end DirichletL

import Analysis.AuxiliaryParameterIndices
import Analysis.AuxiliaryParameterRates

/-!
The actual finite row and column comparison for CDT v2,
supplied TeX 3950-4004. The cutoff limit follows the dimension choice,
and all rounding errors are retained until that limit.
-/

namespace DirichletL

open Filter Set
open scoped Topology

theorem exists_auxiliary_dimension_comparison {m : ℕ} (hm : 1 < m) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ δ < m ∧ ∀ η : ℝ, 0 < η →
      ∀ᶠ h : ℕ in atTop, ∀ᶠ D : ℕ in atTop, ∀ L : ℕ,
        ((m : ℝ) + δ) * D ≤ L → (L : ℝ) ≤ ((m : ℝ) + δ) * D + 1 →
        let N := (auxiliaryFreeIndices m h D ε).card
        let M := (auxiliaryConstraintIndices (m * h) L
          (((m : ℝ) + δ) * D) (((m : ℝ) - δ) * D) ε).card
        0 < N ∧ M < N ∧ (M : ℝ) / (N - M : ℕ) ≤ η := by
  have hm0 : 0 < m := by omega
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  obtain ⟨q, hq, hmesh⟩ := exists_pos_nat_mesh hε
  let C : ℝ := 4 * (q + 1 : ℕ)
  let κ : ℝ := ε ^ 2 / 128
  let r : ℝ := Real.exp (-κ)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  obtain ⟨δ, hδ, hδε, hδm, hδr⟩ := exists_auxiliary_delta hmR hε hκ
  refine ⟨δ, hδ, hδε, hδm, fun η hη => ?_⟩
  let a : ℝ := m - δ
  let b : ℝ := m - δ / 2
  let c : ℝ := m + δ
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hc : 0 < c := by dsimp [c]; linarith
  have hab : a < b := by dsimp [a, b]; linarith
  have hbm : b < m := by dsimp [b]; linarith
  have hac : a ≤ c := by dsimp [a, c]; linarith
  have hrc : r * c < b := by
    change c * r < a at hδr
    nlinarith
  let θ : ℝ := η / (1 + η)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθ1 : θ < 1 := by dsimp [θ]; apply (div_lt_one (by positivity)).mpr; linarith
  have hθeq : θ / (1 - θ) = η := by
    dsimp [θ]
    field_simp
    ring
  have hgeo := tendsto_geometric_sum_div_one_sub (m := m) (C := C) hm0
    (div_nonneg ha.le hb.le) ((div_lt_one hb).mpr hab)
    (div_nonneg (mul_nonneg hr.le hc.le) hb.le) ((div_lt_one hb).mpr hrc) hr.le hr1
  have hrpow : Tendsto (fun h : ℕ => r ^ (m * h)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [pow_mul] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (pow_nonneg hr.le m) (pow_lt_one₀ hr.le hr1 hm0.ne')
  have hg : Tendsto (fun h : ℕ => 1 - C * r ^ (m * h)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (hrpow.const_mul C)
  have he (d : ℕ) : 4 * (q + 1 : ℕ) * Real.exp (-ε ^ 2 * d / 128) = C * r ^ d := by
    dsimp only [C, r, κ]
    rw [show -ε ^ 2 * (d : ℝ) / 128 = (d : ℝ) * (-(ε ^ 2 / 128)) by ring,
      Real.exp_nat_mul]
  filter_upwards [eventually_pow_lt_card_balancedSpeciesIndices hm hb hbm,
    hg.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hgeo.eventually (Iio_mem_nhds hθ), eventually_gt_atTop (0 : ℕ)]
    with h hB hgpos hratio hh
  let d : ℕ := m * h
  let g : ℝ := 1 - C * r ^ d
  have hd : 0 < d := Nat.mul_pos hm0 hh
  change 0 < g at hgpos
  have hbpow := pow_pos hb d
  have hnum : a ^ d + C * r ^ d * c ^ d < θ * g * b ^ d := by
    have ht := mul_lt_mul_of_pos_right ((div_lt_iff₀ hgpos).mp hratio) hbpow
    have heq : ((a / b) ^ d + C * (r * c / b) ^ d) * b ^ d =
        a ^ d + C * r ^ d * c ^ d := by
      rw [div_pow, div_pow, mul_pow]
      field_simp [hbpow.ne']
    change ((a / b) ^ d + C * (r * c / b) ^ d) * b ^ d < θ * g * b ^ d at ht
    rwa [heq] at ht
  have hcut := (tendsto_scaled_cube_majorant a c (C * r ^ d) d).eventually
    (Iio_mem_nhds hnum)
  filter_upwards [hcut, eventually_uniform_lattice_population_mesh (a := 1) (by norm_num) hε,
    eventually_uniform_lattice_population_mesh hc hε] with D hU hDm hLm
  intro L hRL hLR
  have hD : 0 < D := hDm.1
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hDpow := pow_pos hDR d
  have hpopD : 1 / (D : ℝ) ≤ ε / 8 := hDm.2 D (by simp)
  have hpopL : 1 / (L : ℝ) ≤ ε / 8 := hLm.2 L hRL
  have hR : 0 < c * D := mul_pos hc hDR
  have hS : a * D ∈ Set.Icc (0 : ℝ) L :=
    ⟨mul_nonneg ha.le hDR.le, (mul_le_mul_of_nonneg_right hac hDR.le).trans hRL⟩
  let N := (auxiliaryFreeIndices m h D ε).card
  let M := (auxiliaryConstraintIndices d L (c * D) (a * D) ε).card
  have hfree := card_auxiliaryFreeIndices_lower hd hD hq hε hmesh hpopD
  have hconstr := card_auxiliaryConstraintIndices_le hR hRL hLR hS hd hq hε hmesh hpopL
  rw [he] at hfree hconstr
  change g * (balancedSpeciesIndices m h).card * (D : ℝ) ^ d ≤ (N : ℝ) at hfree
  change (M : ℝ) ≤ (a * D + 1) ^ d + C * r ^ d * (L : ℝ) ^ d at hconstr
  have hNlarge : g * b ^ d * (D : ℝ) ^ d ≤ (N : ℝ) := by
    calc
      _ ≤ g * (balancedSpeciesIndices m h).card * (D : ℝ) ^ d := by
        gcongr
      _ ≤ _ := hfree
  have hNpos : 0 < N := by
    exact_mod_cast (mul_pos (mul_pos hgpos hbpow) hDpow).trans_le hNlarge
  have hcutL : (L : ℝ) ≤ (c + 1 / D) * D := by
    calc
      _ ≤ c * D + 1 := hLR
      _ = _ := by field_simp [hDR.ne']
  have hsmall : (a * D + 1) ^ d = (a + 1 / D) ^ d * (D : ℝ) ^ d := by
    rw [← mul_pow]
    congr 1
    field_simp [hDR.ne']
  have hMθ : (M : ℝ) ≤ θ * N := by
    calc
      _ ≤ (a * D + 1) ^ d + C * r ^ d * (L : ℝ) ^ d := hconstr
      _ ≤ (a + 1 / D) ^ d * (D : ℝ) ^ d +
          C * r ^ d * ((c + 1 / D) * D) ^ d := by
        rw [hsmall]
        gcongr
      _ = ((a + 1 / D) ^ d + C * r ^ d * (c + 1 / D) ^ d) * (D : ℝ) ^ d := by
        rw [mul_pow]
        ring
      _ ≤ (θ * g * b ^ d) * (D : ℝ) ^ d := (mul_lt_mul_of_pos_right hU hDpow).le
      _ = θ * (g * b ^ d * (D : ℝ) ^ d) := by ring
      _ ≤ θ * N := mul_le_mul_of_nonneg_left hNlarge hθ.le
  have hrat := nat_dirichlet_ratio_le_of_mul_le hNpos hθ1 hMθ
  change 0 < N ∧ M < N ∧ (M : ℝ) / (N - M : ℕ) ≤ η
  exact ⟨hNpos, hrat.1, by simpa only [hθeq] using hrat.2⟩

end DirichletL

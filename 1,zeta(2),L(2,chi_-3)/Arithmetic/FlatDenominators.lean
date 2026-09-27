import Arithmetic.MonotoneDivisibilityProducts
import Arithmetic.LcmAsymptotic
import Analysis.UniformSequenceLimits

/-!
The two single-step columns and their flat cap for CDT's fourteen-function
family, supplied v2 TeX 3770-3826 and 4304-4404. A real column value
retains the perturbation needed to absorb the fixed coefficient offsets.
-/

namespace DirichletL

open Filter

theorem sum_Ico_natCast_succ {m n : ℕ} (hmn : m ≤ n) :
    (∑ j ∈ Finset.Ico m n, ((j : ℝ) + 1)) =
      ((n : ℝ) * ((n : ℝ) + 1) - (m : ℝ) * ((m : ℝ) + 1)) / 2 := by
  let T : ℕ → ℝ := fun j => (j : ℝ) * ((j : ℝ) + 1) / 2
  calc
    _ = ∑ j ∈ Finset.Ico m n, (T (j + 1) - T j) := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [T]
      push_cast
      ring
    _ = T n - T m := Finset.sum_Ico_sub T hmn
    _ = _ := by dsimp only [T]; ring

/-- The common prefix cap for the two nonzero column blocks. -/
noncomputable def cdt14FlatDenominator (h D : ℕ) (c δ : ℝ) : ℕ :=
  (∏ j ∈ Finset.Ico h (14 * h),
    lcmPrefix ⌊c * (D : ℝ) * (δ + ((j : ℝ) + 1) / (h : ℝ))⌋₊) *
  ∏ j ∈ Finset.Ico (3 * h) (14 * h),
    lcmPrefix ⌊c * (D : ℝ) * (δ + ((j : ℝ) + 1) / (h : ℝ))⌋₊

theorem cdt14FlatDenominator_pos (h D : ℕ) (c δ : ℝ) :
    0 < cdt14FlatDenominator h D c δ :=
  Nat.mul_pos (Finset.prod_pos (fun _ _ => lcmPrefix_pos _))
    (Finset.prod_pos (fun _ _ => lcmPrefix_pos _))

theorem prod_lcmPrefix_dvd_cdt14FlatDenominator (h D : ℕ) {c δ : ℝ} (hc : 0 ≤ c)
    (s₁ s₂ : Finset (Fin (14 * h))) (hs₁ : s₁.card = 13 * h) (hs₂ : s₂.card = 11 * h)
    (r : ℕ → ℕ) (hr : ∀ j < 14 * h,
      (r j : ℝ) ≤ (D : ℝ) * (δ + ((j : ℝ) + 1) / (h : ℝ))) :
    (∏ i ∈ s₁, lcmPrefix ⌊c * (r (i : ℕ) : ℝ)⌋₊) *
      (∏ i ∈ s₂, lcmPrefix ⌊c * (r (i : ℕ) : ℝ)⌋₊) ∣
        cdt14FlatDenominator h D c δ := by
  let N : ℕ → ℕ := fun j => ⌊c * (D : ℝ) * (δ + ((j : ℝ) + 1) / (h : ℝ))⌋₊
  have hN : Monotone N := by
    intro i j hij
    apply Nat.floor_mono
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc (Nat.cast_nonneg D))
    exact add_le_add_left (div_le_div_of_nonneg_right
      (add_le_add_right (by exact_mod_cast hij : (i : ℝ) ≤ j) 1)
      (Nat.cast_nonneg h)) δ
  have hn (j : ℕ) (hj : j < 14 * h) : ⌊c * (r j : ℝ)⌋₊ ≤ N j := by
    apply Nat.floor_mono
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hr j hj) hc
  have hfirst := prod_lcmPrefix_subset_dvd_tail_of_le s₁ 1
    (fun j => ⌊c * (r j : ℝ)⌋₊) N hn (hN.monotoneOn _)
  have hsecond := prod_lcmPrefix_subset_dvd_tail_of_le s₂ 1
    (fun j => ⌊c * (r j : ℝ)⌋₊) N hn (hN.monotoneOn _)
  simp only [one_mul, hs₁, hs₂] at hfirst hsecond
  have h₁ : 14 * h - 13 * h = h := by omega
  have h₂ : 14 * h - 11 * h = 3 * h := by omega
  have hc₁ : 14 * h - h = 13 * h := by omega
  have hc₂ : 14 * h - 3 * h = 11 * h := by omega
  rw [h₁] at hfirst
  rw [h₂] at hsecond
  change _ ∣ (∏ j ∈ Finset.Ico h (14 * h), lcmPrefix (N j)) *
    ∏ j ∈ Finset.Ico (3 * h) (14 * h), lcmPrefix (N j)
  rw [Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range, hc₁, hc₂]
  exact mul_dvd_mul hfirst hsecond

theorem log_cdt14FlatDenominator (h D : ℕ) (c δ : ℝ) :
    Real.log (cdt14FlatDenominator h D c δ : ℝ) =
      (∑ j ∈ Finset.Ico h (14 * h),
        Real.log (lcmPrefix ⌊c * (D : ℝ) * (δ + ((j : ℝ) + 1) / (h : ℝ))⌋₊ : ℝ)) +
      ∑ j ∈ Finset.Ico (3 * h) (14 * h),
        Real.log (lcmPrefix ⌊c * (D : ℝ) * (δ + ((j : ℝ) + 1) / (h : ℝ))⌋₊ : ℝ) := by
  have hpos (s : Finset ℕ) :
      ((∏ j ∈ s, lcmPrefix ⌊c * (D : ℝ) * (δ + ((j : ℝ) + 1) / (h : ℝ))⌋₊ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.prod_pos (fun _ _ => lcmPrefix_pos _)).ne'
  rw [cdt14FlatDenominator, Nat.cast_mul, Real.log_mul (hpos _) (hpos _)]
  simp only [Nat.cast_prod]
  congr 1 <;> apply Real.log_prod <;> intro j _ <;>
    exact_mod_cast (lcmPrefix_pos ⌊c * (D : ℝ) * (δ + ((j : ℝ) + 1) / (h : ℝ))⌋₊).ne'

theorem sum_cdt14_flat_grid {h : ℕ} (hh : 0 < h) (c D δ : ℝ) :
    (∑ j ∈ Finset.Ico h (14 * h), c * D * (δ + ((j : ℝ) + 1) / (h : ℝ))) +
      (∑ j ∈ Finset.Ico (3 * h) (14 * h), c * D * (δ + ((j : ℝ) + 1) / (h : ℝ))) =
        c * D * (191 * (h : ℝ) + 12 + 24 * (h : ℝ) * δ) := by
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have h₁ : h ≤ 14 * h := by omega
  have h₂ : 3 * h ≤ 14 * h := by omega
  have hc₁ : 14 * h - h = 13 * h := by omega
  have hc₂ : 14 * h - 3 * h = 11 * h := by omega
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Nat.card_Ico, nsmul_eq_mul, ← Finset.sum_div, sum_Ico_natCast_succ h₁,
    sum_Ico_natCast_succ h₂, hc₁, hc₂]
  push_cast
  field_simp
  ring

theorem eventually_log_lcmPrefix_floor_grid_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ D : ℕ in atTop, ∀ h : ℕ, 0 < h → ∀ c : ℝ, 0 ≤ c → c ≤ 3 →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ j < 14 * h,
        Real.log (lcmPrefix ⌊c * (D : ℝ) * (δ + ((j : ℝ) + 1) / (h : ℝ))⌋₊ : ℝ) ≤
          c * (D : ℝ) * (δ + ((j : ℝ) + 1) / (h : ℝ)) + η * (D : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_abs_initialSegment_sub_le tendsto_log_lcmPrefix_div
      (div_pos hη (by norm_num : (0 : ℝ) < 45)))
  refine eventually_atTop.mpr ⟨N, ?_⟩
  intro D hDN h hh c hc0 hc3 δ hδ0 hδ1 j hj
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have ht0 : 0 ≤ δ + ((j : ℝ) + 1) / (h : ℝ) :=
    add_nonneg hδ0 (div_nonneg (by positivity) hhR.le)
  have ht14 : ((j : ℝ) + 1) / (h : ℝ) ≤ 14 := by
    apply (div_le_iff₀ hhR).mpr
    exact_mod_cast Nat.succ_le_of_lt hj
  have ht15 : δ + ((j : ℝ) + 1) / (h : ℝ) ≤ 15 := by linarith only [ht14, hδ1]
  have hcD : 0 ≤ c * (D : ℝ) := mul_nonneg hc0 (Nat.cast_nonneg D)
  have harg0 : 0 ≤ c * (D : ℝ) * (δ + ((j : ℝ) + 1) / (h : ℝ)) := mul_nonneg hcD ht0
  have harg : c * (D : ℝ) * (δ + ((j : ℝ) + 1) / (h : ℝ)) ≤ 45 * (D : ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_left ht15 hcD
    have h₂ := mul_le_mul_of_nonneg_right hc3 (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
    nlinarith only [h₁, h₂]
  have hm : ⌊c * (D : ℝ) * (δ + ((j : ℝ) + 1) / (h : ℝ))⌋₊ ≤ 45 * D := by
    apply Nat.floor_le_of_le
    exact_mod_cast harg
  have he := (abs_le.mp (hN (45 * D) (by omega) _ hm)).2
  have hf := Nat.floor_le harg0
  push_cast at he
  linarith only [he, hf]

theorem eventually_log_cdt14FlatDenominator_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ D : ℕ in atTop, ∀ h : ℕ, 0 < h → ∀ c : ℝ, 0 ≤ c → c ≤ 3 →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        Real.log (cdt14FlatDenominator h D c δ : ℝ) ≤
          98 * (h : ℝ) * (D : ℝ) * (191 * c / 98 + 6 * c / (49 * (h : ℝ)) +
            12 * c * δ / 49 + (12 / 49 : ℝ) * η) := by
  filter_upwards [eventually_log_lcmPrefix_floor_grid_le hη] with D hD h hh c hc0 hc3 δ hδ0 hδ1
  have hbound (s : Finset ℕ) (hs : ∀ j ∈ s, j < 14 * h) :
      (∑ j ∈ s,
        Real.log (lcmPrefix ⌊c * (D : ℝ) * (δ + ((j : ℝ) + 1) / (h : ℝ))⌋₊ : ℝ)) ≤
        ∑ j ∈ s, (c * (D : ℝ) * (δ + ((j : ℝ) + 1) / (h : ℝ)) + η * (D : ℝ)) :=
    Finset.sum_le_sum (fun j hj => hD h hh c hc0 hc3 δ hδ0 hδ1 j (hs j hj))
  have hfirst := hbound (Finset.Ico h (14 * h)) (fun _ hj => (Finset.mem_Ico.mp hj).2)
  have hsecond := hbound (Finset.Ico (3 * h) (14 * h)) (fun _ hj => (Finset.mem_Ico.mp hj).2)
  have hup := add_le_add hfirst hsecond
  have hc₁ : 14 * h - h = 13 * h := by omega
  have hc₂ : 14 * h - 3 * h = 11 * h := by omega
  simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico,
    nsmul_eq_mul, hc₁, hc₂] at hup
  push_cast at hup
  rw [log_cdt14FlatDenominator]
  calc
    _ ≤ c * (D : ℝ) * (191 * (h : ℝ) + 12 + 24 * (h : ℝ) * δ) +
        24 * (h : ℝ) * (η * (D : ℝ)) := by
      nlinarith only [hup, sum_cdt14_flat_grid hh c (D : ℝ) δ]
    _ = _ := by field_simp; ring

theorem exists_delta_eventually_log_cdt14FlatDenominator_le {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ₀ δ₀ : ℝ, 0 < ρ₀ ∧ 0 < δ₀ ∧ ∀ᶠ h : ℕ in atTop, ∀ᶠ D : ℕ in atTop,
      ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ ρ₀ → ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ₀ →
        Real.log (cdt14FlatDenominator h D (2 + ρ) δ : ℝ) ≤
          98 * (h : ℝ) * (D : ℝ) * ((191 / 49 : ℝ) + ε) := by
  have hε4 : 0 < ε / 4 := div_pos hε (by norm_num)
  refine ⟨min 1 (ε / 4), min 1 (ε / 4), lt_min (by norm_num) hε4,
    lt_min (by norm_num) hε4, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ), eventually_ge_atTop ⌈4 / ε⌉₊] with h hh hhε
  filter_upwards [eventually_log_cdt14FlatDenominator_le hε4] with D hD ρ hρ0 hρ δ hδ0 hδ
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hlarge : 4 / ε ≤ (h : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hhε)
  have hinv : 1 / (h : ℝ) ≤ ε / 4 := by
    apply (div_le_iff₀ hhR).mpr
    have he := (div_le_iff₀ hε).mp hlarge
    nlinarith only [he]
  have hρ1 : ρ ≤ 1 := hρ.trans (min_le_left _ _)
  have hρ4 : ρ ≤ ε / 4 := hρ.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hδ.trans (min_le_left _ _)
  have hδ4 : δ ≤ ε / 4 := hδ.trans (min_le_right _ _)
  have hc0 : 0 ≤ 2 + ρ := by linarith only [hρ0]
  have hc3 : 2 + ρ ≤ 3 := by linarith only [hρ1]
  have hfinite : 6 * (2 + ρ) / (49 * (h : ℝ)) ≤ (18 / 49 : ℝ) * (ε / 4) := by
    have ha := div_le_div_of_nonneg_right (by linarith only [hc3] : 6 * (2 + ρ) ≤ 18)
      (by positivity : (0 : ℝ) ≤ 49 * (h : ℝ))
    have hb : 18 / (49 * (h : ℝ)) ≤ (18 / 49 : ℝ) * (ε / 4) := by
      convert mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 18 / 49) using 1
      ring
    exact ha.trans hb
  have hshift : 12 * (2 + ρ) * δ / 49 ≤ (36 / 49 : ℝ) * (ε / 4) := by
    have hm := mul_le_mul_of_nonneg_right hc3 hδ0
    nlinarith only [hm, hδ4]
  have herr : 191 * (2 + ρ) / 98 + 6 * (2 + ρ) / (49 * (h : ℝ)) +
      12 * (2 + ρ) * δ / 49 + (12 / 49 : ℝ) * (ε / 4) ≤ (191 / 49 : ℝ) + ε := by
    linarith only [hfinite, hshift, hρ4, hε]
  exact (hD h hh (2 + ρ) hc0 hc3 δ hδ0 hδ1).trans
    (mul_le_mul_of_nonneg_left herr (by positivity))

end DirichletL

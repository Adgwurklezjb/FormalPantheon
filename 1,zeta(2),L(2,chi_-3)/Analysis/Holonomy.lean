import Mathlib

/-!
Finite arithmetic denominator rates used by CDT v2 Section 7. The analytic
holonomy estimate is intentionally separate from this module.
-/

namespace DirichletL

/-! The source numbers rows and columns from one; Lean uses explicit offsets. -/

/-- The sum of the first `r` entries in row `i` of a natural-indexed array. -/
def holonomyRowSum (b : ℕ → ℕ → ℝ) (r i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range r, b i (j + 1)

/-- The flat denominator rate `τᶠˡᵃᵗ` from CDT, with rows `1,...,m`. -/
noncomputable def tauFlat (m r : ℕ) (b : ℕ → ℕ → ℝ) : ℝ :=
  (1 / (m : ℝ) ^ 2) *
    ∑ i ∈ Finset.range m,
      (2 * (i : ℝ) + 1) * holonomyRowSum b r (i + 1)

/-- Odd weights sum to the square of the number of rows. -/
private theorem sum_odd_weights (m : ℕ) :
    ∑ i ∈ Finset.range m, (2 * (i : ℝ) + 1) = (m : ℝ) ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- A nonnegative row array has a nonnegative flat denominator rate. -/
theorem tauFlat_nonneg {m r : ℕ} (hm : 0 < m) (b : ℕ → ℕ → ℝ)
    (hb : ∀ i < m, 0 ≤ holonomyRowSum b r (i + 1)) :
    0 ≤ tauFlat m r b := by
  have hweight : ∀ i ∈ Finset.range m, 0 ≤ (2 * (i : ℝ) + 1) := by
    intro i hi
    positivity
  have hsum : 0 ≤ ∑ i ∈ Finset.range m,
      (2 * (i : ℝ) + 1) * holonomyRowSum b r (i + 1) := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hweight i hi) (hb i (Finset.mem_range.mp hi))
  exact mul_nonneg (by positivity) hsum

/-- The flat rate is bounded by the last row when row sums are monotone upward. -/
theorem tauFlat_le_last {m r : ℕ} (hm : 0 < m) (b : ℕ → ℕ → ℝ)
    (hmono : ∀ i < m, holonomyRowSum b r (i + 1) ≤
      holonomyRowSum b r m) :
    tauFlat m r b ≤ holonomyRowSum b r m := by
  have hweight : ∀ i ∈ Finset.range m, 0 ≤ (2 * (i : ℝ) + 1) := by
    intro i hi
    positivity
  have hsum :
      (∑ i ∈ Finset.range m,
        (2 * (i : ℝ) + 1) * holonomyRowSum b r (i + 1)) ≤
        (∑ i ∈ Finset.range m,
          (2 * (i : ℝ) + 1) * holonomyRowSum b r m) := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (hmono i (Finset.mem_range.mp hi)) (hweight i hi)
  have hscale : 0 ≤ (1 / (m : ℝ) ^ 2) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum hscale
  rw [← Finset.sum_mul, sum_odd_weights] at hscaled
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hmsq : (m : ℝ) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hmreal)
  dsimp [tauFlat]
  calc
    (1 / (m : ℝ) ^ 2) *
        ∑ i ∈ Finset.range m,
          (2 * (i : ℝ) + 1) * holonomyRowSum b r (i + 1) ≤
      (1 / (m : ℝ) ^ 2) * ((m : ℝ) ^ 2 * holonomyRowSum b r m) := hscaled
    _ = holonomyRowSum b r m := by field_simp

/-- The step-shaped column condition used in CDT's denominator array. -/
def HolonomyColumnStep (m r : ℕ) (b : ℕ → ℕ → ℝ)
    (u : ℕ → ℕ) (v : ℕ → ℝ) : Prop :=
  (∀ j < r, u j ≤ m) ∧
    (∀ j < r, ∀ i < u j, b (i + 1) (j + 1) = 0) ∧
      (∀ j < r, ∀ i, u j ≤ i → i < m → b (i + 1) (j + 1) = v j) ∧
        (∀ j < r, u j = m → v j = 0)

private theorem sum_odd_weights_Ico {u m : ℕ} (hu : u ≤ m) :
    ∑ i ∈ Finset.Ico u m, (2 * (i : ℝ) + 1) =
      (m : ℝ) ^ 2 - (u : ℝ) ^ 2 := by
  have h := Finset.sum_range_add_sum_Ico
    (fun i : ℕ => (2 * (i : ℝ) + 1)) hu
  rw [sum_odd_weights, sum_odd_weights] at h
  linarith

private theorem weighted_column_step {m r : ℕ}
    (b : ℕ → ℕ → ℝ) (u : ℕ → ℕ) (v : ℕ → ℝ)
    (hstep : HolonomyColumnStep m r b u v) {j : ℕ} (hj : j < r) :
    (∑ i ∈ Finset.range m,
      (2 * (i : ℝ) + 1) * b (i + 1) (j + 1)) =
      ((m : ℝ) ^ 2 - (u j : ℝ) ^ 2) * v j := by
  have hu : u j ≤ m := hstep.1 j hj
  have hprefix :
      (∑ i ∈ Finset.range (u j),
        (2 * (i : ℝ) + 1) * b (i + 1) (j + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hstep.2.1 j hj i (Finset.mem_range.mp hi), mul_zero]
  have htail :
      (∑ i ∈ Finset.Ico (u j) m,
        (2 * (i : ℝ) + 1) * b (i + 1) (j + 1)) =
        ((m : ℝ) ^ 2 - (u j : ℝ) ^ 2) * v j := by
    calc
      (∑ i ∈ Finset.Ico (u j) m,
          (2 * (i : ℝ) + 1) * b (i + 1) (j + 1)) =
          ∑ i ∈ Finset.Ico (u j) m, (2 * (i : ℝ) + 1) * v j := by
            apply Finset.sum_congr rfl
            intro i hi
            exact congrArg (fun z : ℝ => (2 * (i : ℝ) + 1) * z)
              (hstep.2.2.1 j hj i (Finset.mem_Ico.mp hi).1
                (Finset.mem_Ico.mp hi).2)
      _ = (∑ i ∈ Finset.Ico (u j) m, (2 * (i : ℝ) + 1)) * v j := by
            rw [Finset.sum_mul]
      _ = ((m : ℝ) ^ 2 - (u j : ℝ) ^ 2) * v j := by
            rw [sum_odd_weights_Ico hu]
  rw [← Finset.sum_range_add_sum_Ico
    (fun i : ℕ => (2 * (i : ℝ) + 1) * b (i + 1) (j + 1)) hu,
    hprefix, zero_add, htail]

private theorem last_row_step {m r : ℕ} (hm : 0 < m)
    (b : ℕ → ℕ → ℝ) (u : ℕ → ℕ) (v : ℕ → ℝ)
    (hstep : HolonomyColumnStep m r b u v) :
    holonomyRowSum b r m = ∑ j ∈ Finset.range r, v j := by
  unfold holonomyRowSum
  apply Finset.sum_congr rfl
  intro j hj
  have hu : u j ≤ m := hstep.1 j (Finset.mem_range.mp hj)
  by_cases hum : u j = m
  · have hm1 : m - 1 < u j := by simpa [hum] using Nat.pred_lt (ne_of_gt hm)
    have hz : b ((m - 1) + 1) (j + 1) = 0 :=
      hstep.2.1 j (Finset.mem_range.mp hj) (m - 1) hm1
    have hvm : v j = 0 := hstep.2.2.2 j (Finset.mem_range.mp hj) hum
    simpa [hum, hvm, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hm))]
      using hz
  · have hul : u j < m := lt_of_le_of_ne hu hum
    have hv := hstep.2.2.1 j (Finset.mem_range.mp hj) (m - 1)
      (Nat.le_sub_one_of_lt hul) (Nat.sub_lt (Nat.zero_lt_of_lt hm) (by omega))
    simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hm))] using hv

/-- Exact finite form of CDT's flat denominator-rate identity. -/
theorem tauFlat_eq_last_sub_step {m r : ℕ} (hm : 0 < m)
    (b : ℕ → ℕ → ℝ) (u : ℕ → ℕ) (v : ℕ → ℝ)
    (hstep : HolonomyColumnStep m r b u v) :
    tauFlat m r b = holonomyRowSum b r m -
      (1 / (m : ℝ) ^ 2) *
        ∑ j ∈ Finset.range r, (u j : ℝ) ^ 2 * v j := by
  have hnum :
      (∑ i ∈ Finset.range m,
        (2 * (i : ℝ) + 1) * holonomyRowSum b r (i + 1)) =
        (m : ℝ) ^ 2 * ∑ j ∈ Finset.range r, v j -
          ∑ j ∈ Finset.range r, (u j : ℝ) ^ 2 * v j := by
    calc
      (∑ i ∈ Finset.range m,
          (2 * (i : ℝ) + 1) * holonomyRowSum b r (i + 1)) =
          ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range r,
            (2 * (i : ℝ) + 1) * b (i + 1) (j + 1) := by
              simp [holonomyRowSum, Finset.mul_sum]
      _ = ∑ j ∈ Finset.range r, ∑ i ∈ Finset.range m,
            (2 * (i : ℝ) + 1) * b (i + 1) (j + 1) := by
              rw [Finset.sum_comm]
      _ = ∑ j ∈ Finset.range r,
            (((m : ℝ) ^ 2 - (u j : ℝ) ^ 2) * v j) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact weighted_column_step b u v hstep
                (Finset.mem_range.mp hj)
      _ = (m : ℝ) ^ 2 * ∑ j ∈ Finset.range r, v j -
            ∑ j ∈ Finset.range r, (u j : ℝ) ^ 2 * v j := by
              simp only [sub_mul, Finset.sum_sub_distrib]
              rw [Finset.mul_sum]
  rw [tauFlat, hnum, last_row_step hm b u v hstep]
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hmsq : (m : ℝ) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hmreal)
  field_simp

/-- The fourteen-function denominator array from CDT's numerical example. -/
def cdtDenominator14 (i j : ℕ) : ℝ :=
  if j = 1 then (if i = 1 then 0 else 2)
  else if j = 2 then (if i ≤ 3 then 0 else 2) else 0

/-- The seventeen-function denominator array from CDT's numerical example. -/
def cdtDenominator17 (i j : ℕ) : ℝ :=
  if j = 1 then (if i = 1 then 0 else 2)
  else if j = 2 then (if i ≤ 3 then 0 else 2) else 0

private theorem cdtDenominator14_step :
    HolonomyColumnStep 14 2 cdtDenominator14 (fun j => if j = 0 then 1 else 3)
      (fun _ => 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl <;> norm_num
  · intro j hj i hi
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · norm_num at hi
      have hi' : i = 0 := by omega
      simp [cdtDenominator14, hi']
    · norm_num at hi
      have hi' : i ≤ 2 := by omega
      simp [cdtDenominator14, hi']
  · intro j hj i hui him
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · norm_num at hui
      have hi' : i + 1 ≠ 1 := by omega
      have hi0 : i ≠ 0 := by omega
      simp [cdtDenominator14, hi', hi0]
    · norm_num at hui
      have hi' : 3 < i + 1 := by omega
      have hi2 : 2 < i := by omega
      simp [cdtDenominator14, hi', hi2]
  · intro j hj h
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl <;> norm_num at h

private theorem cdtDenominator17_step :
    HolonomyColumnStep 17 2 cdtDenominator17 (fun j => if j = 0 then 1 else 3)
      (fun _ => 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl <;> norm_num
  · intro j hj i hi
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · norm_num at hi
      have hi' : i = 0 := by omega
      simp [cdtDenominator17, hi']
    · norm_num at hi
      have hi' : i ≤ 2 := by omega
      simp [cdtDenominator17, hi']
  · intro j hj i hui him
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · norm_num at hui
      have hi' : i + 1 ≠ 1 := by omega
      have hi0 : i ≠ 0 := by omega
      simp [cdtDenominator17, hi', hi0]
    · norm_num at hui
      have hi' : 3 < i + 1 := by omega
      have hi2 : 2 < i := by omega
      simp [cdtDenominator17, hi', hi2]
  · intro j hj h
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl <;> norm_num at h

/-- Exact value of the fourteen-function flat rate `191 / 49`. -/
theorem tauFlat_cdtDenominator14 :
    tauFlat 14 2 cdtDenominator14 = (191 / 49 : ℝ) := by
  rw [tauFlat_eq_last_sub_step (by norm_num) cdtDenominator14
    (fun j => if j = 0 then 1 else 3) (fun _ => 2)
    cdtDenominator14_step]
  norm_num [holonomyRowSum, cdtDenominator14, Finset.sum_range_succ]

/-- Exact value of the seventeen-function flat rate `1136 / 289`. -/
theorem tauFlat_cdtDenominator17 :
    tauFlat 17 2 cdtDenominator17 = (1136 / 289 : ℝ) := by
  rw [tauFlat_eq_last_sub_step (by norm_num) cdtDenominator17
    (fun j => if j = 0 then 1 else 3) (fun _ => 2)
    cdtDenominator17_step]
  norm_num [holonomyRowSum, cdtDenominator17, Finset.sum_range_succ]

/-- The integrated lcm cost from CDT v2, Definition `integrated lcm`. -/
noncomputable def integratedLcm (u v w : ℝ) : ℝ :=
  (∫ t in (min u (1 : ℝ))..(1 : ℝ), max (t - w) 0) +
    (∫ t in (max u (1 : ℝ))..v,
      ∑ h ∈ Finset.Icc 1 (Nat.floor ((t - 1) / max (1 : ℝ) w)), 1 / (h : ℝ)) +
      ∫ t in (max u (1 : ℝ))..v,
        max (t / (Nat.floor ((t + max 0 (w - 1)) / max (1 : ℝ) w) : ℝ) - w) 0

/-- Each summand of the integrated lcm cost is nonnegative. -/
theorem integratedLcm_nonneg {u v w : ℝ} (huv : max u 1 ≤ v) :
    0 ≤ integratedLcm u v w := by
  have hfirst : 0 ≤ ∫ t in (min u (1 : ℝ))..(1 : ℝ), max (t - w) 0 := by
    apply intervalIntegral.integral_nonneg (min_le_right u 1)
    intro t ht
    exact le_max_right _ _
  have hsecond : 0 ≤ ∫ t in (max u (1 : ℝ))..v,
      ∑ h ∈ Finset.Icc 1 (Nat.floor ((t - 1) / max (1 : ℝ) w)), 1 / (h : ℝ) := by
    apply intervalIntegral.integral_nonneg huv
    intro t ht
    apply Finset.sum_nonneg
    intro h hh
    exact one_div_nonneg.mpr (Nat.cast_nonneg h)
  have hthird : 0 ≤ ∫ t in (max u (1 : ℝ))..v,
      max (t / (Nat.floor ((t + max 0 (w - 1)) / max (1 : ℝ) w) : ℝ) - w) 0 := by
    apply intervalIntegral.integral_nonneg huv
    intro t ht
    exact le_max_right _ _
  exact add_nonneg (add_nonneg hfirst hsecond) hthird

/-- Sum of the natural integration exponents in rows `1,...,m`. -/
def integrationExponentSum (m : ℕ) (e : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, e (i + 1)

/-- Maximum of the natural integration exponents in rows `1,...,m`. -/
def integrationExponentMax (m : ℕ) (e : ℕ → ℕ) : ℕ :=
  (Finset.range m).sup (fun i => e (i + 1))

/-- The row-wise integration exponents used in CDT's 14- and 17-function arrays. -/
def cdtIntegrationExponents (i : ℕ) : ℕ :=
  if i = 3 ∨ 10 ≤ i then 1 else 0

/-- The fourteen-function source vector has total exponent `6`. -/
theorem integrationExponentSum_cdt14 :
    integrationExponentSum 14 cdtIntegrationExponents = 6 := by
  decide

/-- The seventeen-function source vector has total exponent `9`. -/
theorem integrationExponentSum_cdt17 :
    integrationExponentSum 17 cdtIntegrationExponents = 9 := by
  decide

/-- Both source vectors have maximum integration exponent `1`. -/
theorem integrationExponentMax_cdt (m : ℕ) (hm : 10 ≤ m) :
    integrationExponentMax m cdtIntegrationExponents = 1 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    simp only [cdtIntegrationExponents]
    split_ifs <;> omega
  · have hmem : 2 ∈ Finset.range m := Finset.mem_range.mpr (by omega)
    have hle : cdtIntegrationExponents (2 + 1) ≤
        (Finset.range m).sup (fun i => cdtIntegrationExponents (i + 1)) :=
      Finset.le_sup (s := Finset.range m)
        (f := fun i => cdtIntegrationExponents (i + 1)) hmem
    change 1 ≤ (Finset.range m).sup (fun i => cdtIntegrationExponents (i + 1))
    have hleft : cdtIntegrationExponents (2 + 1) = 1 := by
      norm_num [cdtIntegrationExponents]
    rw [hleft] at hle
    exact hle

/-- The cost minimized in CDT v2 equation `taue`, before multiplication by `2/m^2`. -/
noncomputable def tauSharpCost (m : ℕ) (e : ℕ → ℕ) (ξ : ℝ) : ℝ :=
  ξ * (integrationExponentSum m e : ℝ) +
    (integrationExponentMax m e : ℝ) * integratedLcm ξ m ξ

/-- The infimum version of CDT's integrated denominator rate. -/
noncomputable def tauSharpInfimum (m : ℕ) (e : ℕ → ℕ) : ℝ :=
  (2 / (m : ℝ) ^ 2) *
    sInf (tauSharpCost m e '' Set.Icc 0 (m : ℝ))

/-- The source's fine denominator rate, combining flat and integrated costs. -/
noncomputable def holonomyDenominatorRate (m r : ℕ) (b : ℕ → ℕ → ℝ)
    (e : ℕ → ℕ) : ℝ :=
  tauFlat m r b + tauSharpInfimum m e

/-- Every permitted integration cutoff has nonnegative cost. -/
theorem tauSharpCost_nonneg {m : ℕ} (hm : 0 < m) (e : ℕ → ℕ)
    {ξ : ℝ} (hξ : ξ ∈ Set.Icc 0 (m : ℝ)) :
    0 ≤ tauSharpCost m e ξ := by
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmax : max ξ 1 ≤ (m : ℝ) := max_le hξ.2 hmone
  unfold tauSharpCost
  exact add_nonneg
    (mul_nonneg hξ.1 (Nat.cast_nonneg _))
    (mul_nonneg (Nat.cast_nonneg _) (integratedLcm_nonneg hmax))

/-- The integrated-rate infimum is nonnegative on a nonempty row array. -/
theorem tauSharpInfimum_nonneg {m : ℕ} (hm : 0 < m) (e : ℕ → ℕ) :
    0 ≤ tauSharpInfimum m e := by
  have hnonempty : (tauSharpCost m e '' Set.Icc 0 (m : ℝ)).Nonempty := by
    refine ⟨tauSharpCost m e 0, ?_⟩
    exact ⟨0, ⟨le_rfl, Nat.cast_nonneg m⟩, rfl⟩
  have hbound : ∀ y ∈ tauSharpCost m e '' Set.Icc 0 (m : ℝ), 0 ≤ y := by
    intro y hy
    rcases hy with ⟨ξ, hξ, rfl⟩
    exact tauSharpCost_nonneg hm e hξ
  have hinf : 0 ≤ sInf (tauSharpCost m e '' Set.Icc 0 (m : ℝ)) :=
    le_csInf hnonempty hbound
  exact mul_nonneg (by positivity) hinf

/-- Any permitted cutoff gives an upper bound for the integrated-rate infimum. -/
theorem tauSharpInfimum_le_cost {m : ℕ} (hm : 0 < m) (e : ℕ → ℕ)
    {ξ : ℝ} (hξ : ξ ∈ Set.Icc 0 (m : ℝ)) :
    tauSharpInfimum m e ≤ (2 / (m : ℝ) ^ 2) * tauSharpCost m e ξ := by
  have hbdd : BddBelow (tauSharpCost m e '' Set.Icc 0 (m : ℝ)) := by
    refine bddBelow_def.mpr ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨η, hη, rfl⟩
    exact tauSharpCost_nonneg hm e hη
  have hmem : tauSharpCost m e ξ ∈ tauSharpCost m e '' Set.Icc 0 (m : ℝ) :=
    ⟨ξ, hξ, rfl⟩
  exact mul_le_mul_of_nonneg_left (csInf_le hbdd hmem) (by positivity)

/-- The source's 14-row candidate `ξ = 2` gives an explicit upper bound. -/
theorem tauSharpInfimum_cdt14_le_at_two :
    tauSharpInfimum 14 cdtIntegrationExponents ≤
      (1 / 98 : ℝ) * (12 + integratedLcm 2 14 2) := by
  have h := tauSharpInfimum_le_cost (m := 14) (e := cdtIntegrationExponents)
    (by norm_num) (ξ := 2) (by norm_num)
  norm_num [tauSharpCost, integrationExponentSum_cdt14,
    integrationExponentMax_cdt 14 (by norm_num)] at h ⊢
  exact h

/-- The source's 17-row candidate `ξ = 7/4` gives an explicit upper bound. -/
theorem tauSharpInfimum_cdt17_le_at_seven_fourths :
    tauSharpInfimum 17 cdtIntegrationExponents ≤
      (2 / 289 : ℝ) * (63 / 4 + integratedLcm (7 / 4) 17 (7 / 4)) := by
  have h := tauSharpInfimum_le_cost (m := 17) (e := cdtIntegrationExponents)
    (by norm_num) (ξ := (7 / 4 : ℝ)) (by norm_num)
  norm_num [tauSharpCost, integrationExponentSum_cdt17,
    integrationExponentMax_cdt 17 (by norm_num)] at h ⊢
  exact h

end DirichletL

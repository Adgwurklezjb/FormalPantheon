import Analysis.UniformIntegralGrid
import Analysis.BlockPhaseApproximation

/-!
The signed double maximum integral in CDT v2, supplied TeX 3503-3540
and 4150-4228. Meanings and independent mesh checks precede these bodies
-/

namespace DirichletL

/-- The iterated signed maximum integral of two profiles on the unit interval. -/
noncomputable def pairwiseMaxIntegral (f g : ℝ → ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, max (f u) (g v)

/-- The average maximum over two independently sized regular right grids. -/
noncomputable def pairwiseMaxGridAverage (f g : ℝ → ℝ) (n ℓ : ℕ) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin ℓ,
    max (f (((i.val : ℝ) + 1) / n)) (g (((j.val : ℝ) + 1) / ℓ))) /
      ((n : ℝ) * (ℓ : ℝ))

theorem lipschitzWith_integral_max {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1)) :
    LipschitzWith 1 (fun x : ℝ => ∫ v in (0 : ℝ)..1, max x (g v)) := by
  apply LipschitzWith.mk_one
  intro x y
  have hx : IntervalIntegrable (fun v => max x (g v)) MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (continuousOn_const.sup hg)
  have hy : IntervalIntegrable (fun v => max y (g v)) MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (continuousOn_const.sup hg)
  have hbound : ∀ v ∈ Set.uIoc (0 : ℝ) 1, ‖max x (g v) - max y (g v)‖ ≤ |x - y| := by
    intro v _
    simpa only [Real.norm_eq_abs] using abs_max_sub_max_le_abs x y (g v)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [intervalIntegral.integral_sub hx hy] at h
  simpa only [Real.norm_eq_abs, Real.dist_eq, sub_zero, abs_one, mul_one] using h

theorem abs_pairwiseMaxIntegral_le {f g : ℝ → ℝ} {B : ℝ}
    (hf : ∀ u ∈ Set.Icc (0 : ℝ) 1, |f u| ≤ B)
    (hg : ∀ v ∈ Set.Icc (0 : ℝ) 1, |g v| ≤ B) :
    |pairwiseMaxIntegral f g| ≤ B := by
  have hinner (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      |∫ v in (0 : ℝ)..1, max (f u) (g v)| ≤ B := by
    have hbound : ∀ v ∈ Set.uIoc (0 : ℝ) 1, ‖max (f u) (g v)‖ ≤ B := by
      intro v hv
      rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hv
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(abs_le.mp (hf u hu)).1.trans (le_max_left _ _),
        max_le (abs_le.mp (hf u hu)).2 (abs_le.mp (hg v ⟨hv.1.le, hv.2⟩)).2⟩
    simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hbound : ∀ u ∈ Set.uIoc (0 : ℝ) 1,
      ‖∫ v in (0 : ℝ)..1, max (f u) (g v)‖ ≤ B := by
    intro u hu
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hu
    simpa only [Real.norm_eq_abs] using hinner u ⟨hu.1.le, hu.2⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa only [pairwiseMaxIntegral, Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h

theorem abs_pairwiseMaxGridAverage_sub_integral_le {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    {n ℓ : ℕ} (hn : 0 < n) (hℓ : 0 < ℓ) {ξ η : ℝ}
    (hnmesh : 1 / (n : ℝ) ≤ η) (hℓmesh : 1 / (ℓ : ℝ) ≤ η)
    (hfclose : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |x - y| ≤ η → |f x - f y| ≤ ξ)
    (hgclose : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |x - y| ≤ η → |g x - g y| ≤ ξ) :
    |pairwiseMaxGridAverage f g n ℓ - pairwiseMaxIntegral f g| ≤ 2 * ξ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let J (u : ℝ) : ℝ := ∫ v in (0 : ℝ)..1, max (f u) (g v)
  let A (i : Fin n) : ℝ := (∑ j : Fin ℓ,
    max (f (((i.val : ℝ) + 1) / n)) (g (((j.val : ℝ) + 1) / ℓ))) / ℓ
  have hA (i : Fin n) : |A i - J (((i.val : ℝ) + 1) / n)| ≤ ξ := by
    apply abs_sum_right_grid_sub_integral_le
      (f := fun v => max (f (((i.val : ℝ) + 1) / n)) (g v)) hℓ
      (ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (continuousOn_const.sup hg)) hℓmesh
    intro x hx y hy hxy
    have hmax : |max (f (((i.val : ℝ) + 1) / n)) (g x) -
        max (f (((i.val : ℝ) + 1) / n)) (g y)| ≤ |g x - g y| := by
      simpa only [max_comm] using
        abs_max_sub_max_le_abs (g x) (g y) (f (((i.val : ℝ) + 1) / n))
    exact hmax.trans (hgclose x hx y hy hxy)
  have hmean : |(∑ i, A i) / n - (∑ i : Fin n, J (((i.val : ℝ) + 1) / n)) / n| ≤ ξ := by
    rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hnR]
    calc
      _ ≤ (∑ i : Fin n, |A i - J (((i.val : ℝ) + 1) / n)|) / n :=
        div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hnR.le
      _ ≤ (∑ _i : Fin n, ξ) / n :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => hA i)) hnR.le
      _ = ξ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp [hnR.ne']
  have hJ : ContinuousOn J (Set.Icc (0 : ℝ) 1) :=
    (lipschitzWith_integral_max hg).continuous.comp_continuousOn hf
  have houter : |(∑ i : Fin n, J (((i.val : ℝ) + 1) / n)) / n -
      ∫ u in (0 : ℝ)..1, J u| ≤ ξ := by
    apply abs_sum_right_grid_sub_integral_le hn
      (ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hJ) hnmesh
    intro x hx y hy hxy
    have h := (lipschitzWith_integral_max hg).dist_le_mul (f x) (f y)
    have h' : |J x - J y| ≤ |f x - f y| := by
      simpa only [J, Real.dist_eq, NNReal.coe_one, one_mul] using h
    exact h'.trans (hfclose x hx y hy hxy)
  have hnormalize : pairwiseMaxGridAverage f g n ℓ = (∑ i, A i) / n := by
    dsimp only [pairwiseMaxGridAverage, A]
    rw [← Finset.sum_div, div_div, mul_comm (ℓ : ℝ) (n : ℝ)]
  rw [hnormalize]
  change |(∑ i, A i) / n - ∫ u in (0 : ℝ)..1, J u| ≤ 2 * ξ
  calc
    _ ≤ |(∑ i, A i) / n - (∑ i : Fin n, J (((i.val : ℝ) + 1) / n)) / n| +
        |(∑ i : Fin n, J (((i.val : ℝ) + 1) / n)) / n - ∫ u in (0 : ℝ)..1, J u| :=
      abs_sub_le _ _ _
    _ ≤ ξ + ξ := add_le_add hmean houter
    _ = 2 * ξ := by ring

theorem exists_uniform_pairwiseMaxGridAverage_tolerance {κ : Type*} [Fintype κ]
    (f : κ → ℝ → ℝ) (hf : ∀ q, ContinuousOn (f q) (Set.Icc (0 : ℝ) 1))
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ η : ℝ, 0 < η ∧ ∀ q r : κ, ∀ n ℓ : ℕ, 0 < n → 0 < ℓ →
      1 / (n : ℝ) ≤ η → 1 / (ℓ : ℝ) ≤ η →
      |pairwiseMaxGridAverage (f q) (f r) n ℓ - pairwiseMaxIntegral (f q) (f r)| ≤ 2 * ξ := by
  obtain ⟨η, hη, hclose⟩ := exists_uniform_profile_tolerance f hf hξ
  refine ⟨η, hη, ?_⟩
  intro q r n ℓ hn hℓ hnmesh hℓmesh
  exact abs_pairwiseMaxGridAverage_sub_integral_le (hf q) (hf r) hn hℓ hnmesh hℓmesh
    (hclose q) (hclose r)

end DirichletL

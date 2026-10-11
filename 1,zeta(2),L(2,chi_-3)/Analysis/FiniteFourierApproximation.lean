import Analysis.CircleEmpiricalDeviation

/-!
Finite Fourier tests for the circle discrepancy argument in CDT v2,
supplied TeX 4054-4067, and published UDC Lemma 2.5.9. The uniform norm,
finite supports, and dimension-independent choices are checked before these
-/

namespace DirichletL

open MeasureTheory
open scoped Classical Topology

attribute [local instance] fact_one_pos

theorem exists_unitCircle_fourier_approx (f : C(AddCircle (1 : ℝ), ℂ))
    {η : ℝ} (hη : 0 < η) :
    ∃ c : ℤ →₀ ℂ, ‖f - c.sum (fun n a => a • fourier n)‖ < η := by
  have hmem : f ∈ (Submodule.span ℂ (Set.range (@fourier (1 : ℝ)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  change f ∈ closure ((Submodule.span ℂ (Set.range (@fourier (1 : ℝ)))) :
    Set C(AddCircle (1 : ℝ), ℂ)) at hmem
  obtain ⟨p, hp, hfp⟩ := Metric.mem_closure_iff.mp hmem η hη
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hp
  exact ⟨c, by simpa only [dist_eq_norm] using hfp⟩

theorem norm_circleEmpiricalDeviation_fourier_sum_le {d K : ℕ} (hd : 0 < d)
    {a : ℝ} (ha : 0 ≤ a) (t : Fin d → AddCircle (1 : ℝ))
    (hmode : ∀ m : ℕ, 0 < m → m ≤ K → ‖∑ i, fourier 1 (t i) ^ m‖ ≤ a * (d : ℝ))
    (c : ℤ →₀ ℂ) (hsupport : ∀ n ∈ c.support, n.natAbs ≤ K) :
    ‖circleEmpiricalDeviation t (c.sum (fun n b => b • fourier n))‖ ≤
      (∑ n ∈ c.support, ‖c n‖) * a := by
  simp only [Finsupp.sum, map_sum, map_smul, smul_eq_mul]
  calc
    ‖∑ n ∈ c.support, c n * circleEmpiricalDeviation t (fourier n)‖ ≤
        ∑ n ∈ c.support, ‖c n * circleEmpiricalDeviation t (fourier n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ c.support, ‖c n‖ * a := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_circleEmpiricalDeviation_fourier_le hd ha t hmode n (hsupport n hn))
        (norm_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

theorem norm_circleEmpiricalDeviation_le_of_fourier_approx {d K : ℕ} (hd : 0 < d)
    {a : ℝ} (ha : 0 ≤ a) (t : Fin d → AddCircle (1 : ℝ))
    (hmode : ∀ m : ℕ, 0 < m → m ≤ K → ‖∑ i, fourier 1 (t i) ^ m‖ ≤ a * (d : ℝ))
    (c : ℤ →₀ ℂ) (hsupport : ∀ n ∈ c.support, n.natAbs ≤ K)
    {f : C(AddCircle (1 : ℝ), ℂ)} {η : ℝ}
    (happrox : ‖f - c.sum (fun n b => b • fourier n)‖ ≤ η) :
    ‖circleEmpiricalDeviation t f‖ ≤ 2 * η + (∑ n ∈ c.support, ‖c n‖) * a := by
  let P : C(AddCircle (1 : ℝ), ℂ) := c.sum (fun n b => b • fourier n)
  calc
    ‖circleEmpiricalDeviation t f‖ =
        ‖circleEmpiricalDeviation t (f - P) + circleEmpiricalDeviation t P‖ := by
      rw [map_sub, sub_add_cancel]
    _ ≤ ‖circleEmpiricalDeviation t (f - P)‖ + ‖circleEmpiricalDeviation t P‖ := norm_add_le _ _
    _ ≤ 2 * η + (∑ n ∈ c.support, ‖c n‖) * a :=
      add_le_add ((norm_circleEmpiricalDeviation_le hd t (f - P)).trans
        (mul_le_mul_of_nonneg_left happrox (by norm_num)))
        (norm_circleEmpiricalDeviation_fourier_sum_le hd ha t hmode c hsupport)

theorem exists_fourier_control_finite_family {σ : Type*} [Fintype σ]
    (f : σ → C(AddCircle (1 : ℝ), ℝ)) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℕ, 0 < K ∧ ∃ a : ℝ, 0 < a ∧
      ∀ d : ℕ, 0 < d → ∀ t : Fin d → AddCircle (1 : ℝ),
        (∀ m : ℕ, 0 < m → m ≤ K → ‖∑ i, fourier 1 (t i) ^ m‖ ≤ a * (d : ℝ)) →
        ∀ s : σ, |(∑ i, f s (t i)) / (d : ℝ) - ∫ x, f s x ∂AddCircle.haarAddCircle| ≤ η := by
  let F (s : σ) : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun x => (f s x : ℂ), Complex.continuous_ofReal.comp (f s).continuous⟩
  choose c hc using fun s : σ => exists_unitCircle_fourier_approx (F s)
    (by positivity : 0 < η / 4)
  let B : ℝ := 1 + ∑ s, ∑ n ∈ (c s).support, ‖c s n‖
  let K : ℕ := 1 + ∑ s, ∑ n ∈ (c s).support, n.natAbs
  refine ⟨K, by dsimp only [K]; omega, η / (2 * B), by positivity, ?_⟩
  intro d hd t hmode s
  have hsupport (n : ℤ) (hn : n ∈ (c s).support) : n.natAbs ≤ K := by
    have h₁ : n.natAbs ≤ ∑ n ∈ (c s).support, n.natAbs :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hn
    have h₂ : (∑ n ∈ (c s).support, n.natAbs) ≤
        ∑ j : σ, ∑ n ∈ (c j).support, n.natAbs :=
      Finset.single_le_sum
        (f := fun j : σ => ∑ n ∈ (c j).support, n.natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
    dsimp only [K]
    omega
  have hcoef : (∑ n ∈ (c s).support, ‖c s n‖) ≤ B := by
    have h := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : σ => ∑ n ∈ (c j).support, ‖c j n‖)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ s)
    dsimp only [B]
    linarith only [h]
  have herror := norm_circleEmpiricalDeviation_le_of_fourier_approx hd
    (by positivity : 0 ≤ η / (2 * B)) t hmode (c s) hsupport (hc s).le
  have hbound : ‖circleEmpiricalDeviation t (F s)‖ ≤ η := by
    refine herror.trans ?_
    calc
      2 * (η / 4) + (∑ n ∈ (c s).support, ‖c s n‖) * (η / (2 * B)) ≤
          2 * (η / 4) + B * (η / (2 * B)) :=
        add_le_add_left (mul_le_mul_of_nonneg_right hcoef (by positivity)) _
      _ = η := by
        field_simp [show B ≠ 0 by dsimp [B]; positivity]
        ring
  have heq : circleEmpiricalDeviation t (F s) =
      (((∑ i, f s (t i)) / (d : ℝ) - ∫ x, f s x ∂AddCircle.haarAddCircle : ℝ) : ℂ) := by
    rw [circleEmpiricalDeviation_apply]
    change ((∑ i, (f s (t i) : ℂ)) / (d : ℂ) -
      ∫ x, (f s x : ℂ) ∂AddCircle.haarAddCircle) = _
    rw [integral_complex_ofReal]
    push_cast
    rfl
  simpa only [heq, Complex.norm_real, Real.norm_eq_abs] using hbound

end DirichletL

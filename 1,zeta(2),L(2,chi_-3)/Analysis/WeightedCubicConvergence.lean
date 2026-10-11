import Analysis.WeightedCubicEisenstein

/-!
Convergence and holomorphicity of the full weighted lattice sums for
CDT v2, Section 11.1, and Zagier (2009), Section 6.
-/

namespace DirichletL

open Complex Filter EisensteinSeries
open _root_.UpperHalfPlane
open scoped Topology Manifold UpperHalfPlane

theorem summable_norm_weightedCubicEisenstein (w : (Fin 2 → ZMod 6) → ℂ) (τ : ℍ) :
    Summable (fun v : Fin 2 → ℤ =>
      ‖w (fun i => (v i : ZMod 6)) * eisSummand 3 v τ‖) := by
  refine ((summable_norm_eisSummand (by norm_num : (3 : ℤ) ≤ 3) τ).mul_left ‖w‖).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun v => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_le_pi_norm w _) (norm_nonneg _)

theorem norm_weightedCubicSummand_le (w : (Fin 2 → ZMod 6) → ℂ) (v : Fin 2 → ℤ)
    {τ : ℍ} {A B : ℝ} (hB : 0 < B) (hτ : τ ∈ verticalStrip A B) :
    ‖w (fun i => (v i : ZMod 6)) * eisSummand 3 v τ‖ ≤
      ‖w‖ * (r ⟨⟨A, B⟩, hB⟩ ^ (-3 : ℤ) * ‖v‖ ^ (-3 : ℤ)) := by
  have he : ‖eisSummand 3 v τ‖ ≤ r ⟨⟨A, B⟩, hB⟩ ^ (-3 : ℤ) * ‖v‖ ^ (-3 : ℤ) := by
    simpa only [eisSummand, norm_zpow, ← Real.rpow_intCast, Int.cast_neg,
      Int.cast_ofNat] using
      summand_bound_of_mem_verticalStrip (by norm_num : (0 : ℝ) ≤ 3) v hB hτ
  rw [norm_mul]
  exact mul_le_mul (norm_le_pi_norm w _) he (norm_nonneg _) (norm_nonneg _)

theorem weightedCubicEisenstein_tendstoLocallyUniformly
    (w : (Fin 2 → ZMod 6) → ℂ) :
    TendstoLocallyUniformly (fun s : Finset (Fin 2 → ℤ) => fun τ : ℍ =>
      ∑ v ∈ s, w (fun i => (v i : ZMod 6)) * eisSummand 3 v τ)
      (weightedCubicEisenstein w) atTop := by
  have hs : Summable (fun v : Fin 2 → ℤ => ‖v‖ ^ (-3 : ℤ)) := by
    exact_mod_cast summable_one_div_norm_rpow (by norm_num : (2 : ℝ) < 3)
  simp only [tendstoLocallyUniformly_iff_forall_isCompact, weightedCubicEisenstein]
  intro K hK
  obtain ⟨A, B, hB, hKAB⟩ := subset_verticalStrip_of_isCompact hK
  exact (tendstoUniformlyOn_tsum
    (hu := (hs.mul_left (r ⟨⟨A, B⟩, hB⟩ ^ (-3 : ℤ))).mul_left ‖w‖)
    (fun v τ hτ => norm_weightedCubicSummand_le w v hB hτ)).mono hKAB

theorem weightedCubicEisenstein_tendstoLocallyUniformlyOn
    (w : (Fin 2 → ZMod 6) → ℂ) :
    TendstoLocallyUniformlyOn (fun s : Finset (Fin 2 → ℤ) =>
      ↑ₕ(fun τ : ℍ => ∑ v ∈ s, w (fun i => (v i : ZMod 6)) * eisSummand 3 v τ))
      (↑ₕweightedCubicEisenstein w) atTop {z : ℂ | 0 < z.im} := by
  rw [← Subtype.coe_image_univ {z : ℂ | 0 < z.im}]
  apply TendstoLocallyUniformlyOn.comp (s := ⊤) _ _ _ (OpenPartialHomeomorph.continuousOn_symm _)
  · simp only [Set.top_eq_univ, tendstoLocallyUniformlyOn_univ]
    exact weightedCubicEisenstein_tendstoLocallyUniformly w
  · exact fun _ _ => Set.mem_univ _

theorem weightedCubicEisenstein_MDifferentiable (w : (Fin 2 → ZMod 6) → ℂ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (weightedCubicEisenstein w) := by
  intro τ
  suffices DifferentiableAt ℂ (↑ₕweightedCubicEisenstein w) τ.1 by
    convert MDifferentiableAt.comp τ (DifferentiableAt.mdifferentiableAt this) τ.mdifferentiable_coe
    exact funext fun z => (comp_ofComplex (weightedCubicEisenstein w) z).symm
  refine DifferentiableOn.differentiableAt ?_
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.2)
  apply (weightedCubicEisenstein_tendstoLocallyUniformlyOn w).differentiableOn
    (Eventually.of_forall fun s => ?_) (isOpen_lt continuous_const continuous_im)
  exact DifferentiableOn.fun_sum fun v _ =>
    (eisSummand_extension_differentiableOn 3 v).const_mul (w (fun i => (v i : ZMod 6)))

end DirichletL

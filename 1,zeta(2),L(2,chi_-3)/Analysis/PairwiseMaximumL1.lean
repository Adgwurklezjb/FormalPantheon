import Analysis.PairwiseMaximumIntegral

/-!
L1 control of CDT v2's signed maximum integral, supplied TeX 3505-3540 and 4150-4153.
Meanings and normalization checks precede these bodies in
-/

open Filter MeasureTheory Set
open scoped Topology

namespace DirichletL

theorem integrable_pairwiseMaxKernel {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f g : ℝ → ℝ}
    (hf : Integrable f μ) (hg : Integrable g ν) :
    Integrable (fun z : ℝ × ℝ => max (f z.1) (g z.2)) (μ.prod ν) := by
  have hfst : Integrable (fun z : ℝ × ℝ => f z.1) (μ.prod ν) := by
    simpa only [mul_one] using hf.mul_prod (integrable_const (1 : ℝ) (μ := ν))
  have hsnd : Integrable (fun z : ℝ × ℝ => g z.2) (μ.prod ν) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ) (μ := μ)).mul_prod hg
  exact hfst.sup hsnd

theorem pairwiseMaxIntegral_eq_integral_prod {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1) :
    pairwiseMaxIntegral f g = ∫ z : ℝ × ℝ, max (f z.1) (g z.2)
      ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  rw [pairwiseMaxIntegral]
  simp_rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact (integral_prod _ (integrable_pairwiseMaxKernel hf.1 hg.1)).symm

theorem abs_pairwiseMaxIntegral_sub_le {f g f₀ g₀ : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1)
    (hf₀ : IntervalIntegrable f₀ volume 0 1) (hg₀ : IntervalIntegrable g₀ volume 0 1) :
    |pairwiseMaxIntegral f g - pairwiseMaxIntegral f₀ g₀| ≤
      (∫ u in (0 : ℝ)..1, |f u - f₀ u|) + ∫ v in (0 : ℝ)..1, |g v - g₀ v| := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have hmass : μ.real univ = 1 := by simp [μ, measureReal_def]
  have hA : Integrable (fun z : ℝ × ℝ => |f z.1 - f₀ z.1|) (μ.prod μ) := by
    simpa only [mul_one] using
      (hf.1.sub hf₀.1).abs.mul_prod (integrable_const (1 : ℝ) (μ := μ))
  have hB : Integrable (fun z : ℝ × ℝ => |g z.2 - g₀ z.2|) (μ.prod μ) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) (μ := μ)).mul_prod (hg.1.sub hg₀.1).abs
  have hbound (z : ℝ × ℝ) :
      ‖max (f z.1) (g z.2) - max (f₀ z.1) (g₀ z.2)‖ ≤
        |f z.1 - f₀ z.1| + |g z.2 - g₀ z.2| := by
    rw [Real.norm_eq_abs]
    refine (abs_sub_le _ (max (f₀ z.1) (g z.2)) _).trans (add_le_add ?_ ?_)
    · exact abs_max_sub_max_le_abs _ _ _
    · simpa only [max_comm] using abs_max_sub_max_le_abs (g z.2) (g₀ z.2) (f₀ z.1)
  rw [pairwiseMaxIntegral_eq_integral_prod hf hg,
    pairwiseMaxIntegral_eq_integral_prod hf₀ hg₀,
    ← integral_sub (integrable_pairwiseMaxKernel hf.1 hg.1)
      (integrable_pairwiseMaxKernel hf₀.1 hg₀.1)]
  calc
    _ ≤ ∫ z : ℝ × ℝ, |f z.1 - f₀ z.1| + |g z.2 - g₀ z.2| ∂μ.prod μ := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_of_norm_le (hA.add hB) (Eventually.of_forall hbound)
    _ = (∫ u in (0 : ℝ)..1, |f u - f₀ u|) + ∫ v in (0 : ℝ)..1, |g v - g₀ v| := by
      rw [integral_add hA hB,
        integral_fun_fst (μ := μ) (ν := μ) (fun u => |f u - f₀ u|),
        integral_fun_snd (μ := μ) (ν := μ) (fun v => |g v - g₀ v|),
        hmass, one_smul, one_smul]
      simp only [μ, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]

theorem tendsto_pairwiseMaxIntegral_of_L1 {α : Type*} {l : Filter α}
    {f g : α → ℝ → ℝ} {f₀ g₀ : ℝ → ℝ}
    (hf₀ : IntervalIntegrable f₀ volume 0 1) (hg₀ : IntervalIntegrable g₀ volume 0 1)
    (hf : ∀ᶠ a in l, IntervalIntegrable (f a) volume 0 1)
    (hg : ∀ᶠ a in l, IntervalIntegrable (g a) volume 0 1)
    (hfL1 : Tendsto (fun a => ∫ u in (0 : ℝ)..1, |f a u - f₀ u|) l (𝓝 0))
    (hgL1 : Tendsto (fun a => ∫ v in (0 : ℝ)..1, |g a v - g₀ v|) l (𝓝 0)) :
    Tendsto (fun a => pairwiseMaxIntegral (f a) (g a)) l
      (𝓝 (pairwiseMaxIntegral f₀ g₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
    (by simpa only [zero_add] using hfL1.add hgL1)
  filter_upwards [hf, hg] with a hfa hga
  simpa only [Real.norm_eq_abs] using abs_pairwiseMaxIntegral_sub_le hfa hga hf₀ hg₀

end DirichletL

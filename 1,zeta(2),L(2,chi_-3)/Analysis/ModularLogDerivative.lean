import Analysis.ModularSlash

/-!
Normalized logarithmic derivatives for Zagier (2009), Section 5,
equation (7), and CDT v2 Section 11.1. The weight-two transformation
is differentiated on the open upper half-plane, without a logarithm branch.
-/

namespace DirichletL

open Complex Filter
open _root_.UpperHalfPlane hiding I
open scoped Topology Manifold MatrixGroups ModularForm Real

theorem logDeriv_eq_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
    (h : f =ᶠ[𝓝 z] g) : logDeriv f z = logDeriv g z := by
  simp only [logDeriv_apply, h.deriv_eq, h.eq_of_nhds]

theorem hasDerivAt_SL2_smul_ofComplex (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (fun w : ℂ => ((γ • ofComplex w : ℍ) : ℂ))
      (1 / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ^ 2) z := by
  have hd : ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ≠ 0 :=
    denom_ne_zero γ ⟨z, hz⟩
  have hdet : (γ 0 0 : ℂ) * (γ 1 1 : ℂ) - (γ 0 1 : ℂ) * (γ 1 0 : ℂ) = 1 := by
    have h := γ.property
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have hnum : (γ 0 0 : ℂ) * ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) -
      ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) * (γ 1 0 : ℂ) = 1 := by
    linear_combination hdet
  have h := (((hasDerivAt_id z).const_mul (γ 0 0 : ℂ)).add_const (γ 0 1 : ℂ)).div
    (((hasDerivAt_id z).const_mul (γ 1 0 : ℂ)).add_const (γ 1 1 : ℂ)) hd
  simp only [id_eq, mul_one, hnum] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with w hw
  simp only [ofComplex_apply_of_im_pos hw]
  simpa [num, denom] using
    (coe_smul_of_det_pos (g := (γ : GL (Fin 2) ℝ)) (by simp) ⟨w, hw⟩)

/-- The logarithmic derivative normalized by the modular parameter q=exp(2*pi*i*tau). -/
noncomputable def modularLogDeriv (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  logDeriv f z / (2 * π * I)

theorem differentiableOn_modularLogDeriv {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | 0 < z.im})
    (h0 : ∀ z : ℂ, 0 < z.im → f z ≠ 0) :
    DifferentiableOn ℂ (modularLogDeriv f) {z | 0 < z.im} := by
  exact ((hf.deriv (isOpen_lt continuous_const Complex.continuous_im)).div hf h0).div_const _

theorem mdifferentiable_modularLogDeriv {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | 0 < z.im})
    (h0 : ∀ z : ℂ, 0 < z.im → f z ≠ 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => modularLogDeriv f τ) := by
  apply UpperHalfPlane.mdifferentiable_iff.mpr
  apply (differentiableOn_modularLogDeriv hf h0).congr
  intro z hz
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, UpperHalfPlane.coe_mk]
  rfl

theorem modularLogDeriv_slash_SL2 {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | 0 < z.im}) (γ : SL(2, ℤ)) :
    (fun τ : ℍ => modularLogDeriv f τ) ∣[(2 : ℤ)] γ =
      fun τ : ℍ => modularLogDeriv (fun z : ℂ => f ((γ • ofComplex z : ℍ) : ℂ)) τ := by
  ext τ
  have hg := hasDerivAt_SL2_smul_ofComplex γ τ.im_pos
  have hfg : DifferentiableAt ℂ f ((γ • ofComplex (τ : ℂ) : ℍ) : ℂ) := by
    rw [ofComplex_apply]
    exact hf.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds (γ • τ : ℍ).im_pos)
  have h := logDeriv_comp (g := fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ))
    (x := (τ : ℂ)) hfg hg.differentiableAt
  rw [hg.deriv] at h
  simp only [Function.comp_def, ofComplex_apply] at h
  simp only [ModularForm.SL_slash_def, UpperHalfPlane.denom, zpow_neg,
    zpow_ofNat, modularLogDeriv]
  change logDeriv f ((γ • τ : ℍ) : ℂ) / (2 * π * I) *
    (((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ 2)⁻¹ = _
  rw [h]
  ring

theorem modularLogDeriv_slash_of_invariant {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | 0 < z.im}) (γ : SL(2, ℤ))
    (hinv : ∀ τ : ℍ, f ((γ • τ : ℍ) : ℂ) = f τ) :
    (fun τ : ℍ => modularLogDeriv f τ) ∣[(2 : ℤ)] γ = fun τ : ℍ => modularLogDeriv f τ := by
  rw [modularLogDeriv_slash_SL2 hf]
  ext τ
  apply congrArg (fun w : ℂ => w / (2 * π * I))
  apply logDeriv_eq_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos] with z hz
  simpa only [ofComplex_apply_of_im_pos hz] using hinv ⟨z, hz⟩

end DirichletL

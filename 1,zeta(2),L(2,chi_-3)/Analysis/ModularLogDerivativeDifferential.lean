import Analysis.ModularLogDerivative

/-!
The weight-four logarithmic differential for Zagier (2009), Section 5,
equation (7). For a nonvanishing weight-two function G, the expression
L^2 - 2*D(L), where L = D(G)/G and D = (2*pi*i)^(-1)*d/dtau,
-/

namespace DirichletL

open Complex Filter
open _root_.UpperHalfPlane hiding I
open scoped Topology Manifold MatrixGroups ModularForm Real

theorem modularLogDeriv_const_mul (f : ℂ → ℂ) {a : ℂ} (ha : a ≠ 0) :
    modularLogDeriv (fun z => a * f z) = modularLogDeriv f := by
  ext z
  simp only [modularLogDeriv, logDeriv_const_mul z a ha]

/-- The normalized weight-four logarithmic differential of a weight-two function. -/
noncomputable def modularLogDerivCorrection (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  modularLogDeriv f z ^ 2 - 2 * deriv (modularLogDeriv f) z / (2 * π * I)

theorem modularLogDerivCorrection_const_mul (f : ℂ → ℂ) {a : ℂ} (ha : a ≠ 0) :
    modularLogDerivCorrection (fun z => a * f z) = modularLogDerivCorrection f := by
  unfold modularLogDerivCorrection
  rw [modularLogDeriv_const_mul f ha]

theorem differentiableOn_modularLogDerivCorrection {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | 0 < z.im})
    (h0 : ∀ z : ℂ, 0 < z.im → f z ≠ 0) :
    DifferentiableOn ℂ (modularLogDerivCorrection f) {z | 0 < z.im} := by
  have hL := differentiableOn_modularLogDeriv hf h0
  exact (hL.pow 2).sub
    ((hL.deriv (isOpen_lt continuous_const Complex.continuous_im)).const_mul 2 |>.div_const _)

theorem mdifferentiable_modularLogDerivCorrection {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | 0 < z.im})
    (h0 : ∀ z : ℂ, 0 < z.im → f z ≠ 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => modularLogDerivCorrection f τ) := by
  apply UpperHalfPlane.mdifferentiable_iff.mpr
  apply (differentiableOn_modularLogDerivCorrection hf h0).congr
  intro z hz
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, UpperHalfPlane.coe_mk]
  rfl

theorem modularLogDeriv_weightTwo_relation {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | 0 < z.im})
    (hg : DifferentiableOn ℂ g {z | 0 < z.im})
    (hg0 : ∀ z : ℂ, 0 < z.im → g z ≠ 0) (γ : SL(2, ℤ))
    (hrel : ∀ τ : ℍ, f ((γ • τ : ℍ) : ℂ) =
      ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ 2 * g τ) (τ : ℍ) :
    modularLogDeriv f ((γ • τ : ℍ) : ℂ) =
      ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ 2 * modularLogDeriv g τ +
        2 * (γ 1 0 : ℂ) * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) / (2 * π * I) := by
  let j : ℂ := (γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)
  have hj : j ≠ 0 := denom_ne_zero γ τ
  have hd : (2 * π * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hJ : HasDerivAt (fun z : ℂ => (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ))
      (γ 1 0 : ℂ) (τ : ℂ) := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id (τ : ℂ)).const_mul (γ 1 0 : ℂ)).add_const (γ 1 1 : ℂ)
  have hge := hg.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos)
  have he : (fun z : ℂ => f ((γ • ofComplex z : ℍ) : ℂ)) =ᶠ[𝓝 (τ : ℂ)]
      (fun z : ℂ => ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ^ 2 * g z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos]
      with z hz
    simpa only [ofComplex_apply_of_im_pos hz, UpperHalfPlane.coe_mk] using hrel ⟨z, hz⟩
  have hlog : modularLogDeriv (fun z : ℂ => f ((γ • ofComplex z : ℍ) : ℂ)) τ =
      modularLogDeriv g τ + 2 * (γ 1 0 : ℂ) / ((2 * π * I) * j) := by
    unfold modularLogDeriv
    rw [logDeriv_eq_of_eventuallyEq he,
      logDeriv_mul (f := fun z : ℂ => ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ^ 2)
        (g := g) (τ : ℂ) (pow_ne_zero 2 hj) (hg0 τ τ.im_pos)
        (hJ.differentiableAt.pow 2) hge,
      logDeriv_fun_pow hJ.differentiableAt, logDeriv_apply, hJ.deriv]
    change (2 * ((γ 1 0 : ℂ) / j) + logDeriv g τ) / (2 * π * I) = _
    field_simp [hj, hd]
    ring
  have hs := congrFun (modularLogDeriv_slash_SL2 hf γ) τ
  simp only [ModularForm.SL_slash_def, UpperHalfPlane.denom,
    zpow_neg, zpow_ofNat] at hs
  change modularLogDeriv f ((γ • τ : ℍ) : ℂ) * (j ^ 2)⁻¹ = _ at hs
  rw [hlog] at hs
  have hs' := (mul_inv_eq_iff_eq_mul₀ (pow_ne_zero 2 hj)).mp hs
  change modularLogDeriv f ((γ • τ : ℍ) : ℂ) =
    j ^ 2 * modularLogDeriv g τ + 2 * (γ 1 0 : ℂ) * j / (2 * π * I)
  rw [hs']
  field_simp [hj, hd]

theorem deriv_modularLogDeriv_weightTwo_relation {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | 0 < z.im})
    (hg : DifferentiableOn ℂ g {z | 0 < z.im})
    (hf0 : ∀ z : ℂ, 0 < z.im → f z ≠ 0)
    (hg0 : ∀ z : ℂ, 0 < z.im → g z ≠ 0) (γ : SL(2, ℤ))
    (hrel : ∀ τ : ℍ, f ((γ • τ : ℍ) : ℂ) =
      ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ 2 * g τ) (τ : ℍ) :
    deriv (modularLogDeriv f) ((γ • τ : ℍ) : ℂ) =
      ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ 4 * deriv (modularLogDeriv g) τ +
        2 * (γ 1 0 : ℂ) * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ 3 *
          modularLogDeriv g τ +
        2 * (γ 1 0 : ℂ) ^ 2 * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ 2 /
          (2 * π * I) := by
  let j : ℂ := (γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)
  have hj : j ≠ 0 := denom_ne_zero γ τ
  have hLf := (differentiableOn_modularLogDeriv hf hf0).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds (γ • τ : ℍ).im_pos)
  have hLg := (differentiableOn_modularLogDeriv hg hg0).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos)
  have hJ : HasDerivAt (fun z : ℂ => (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ))
      (γ 1 0 : ℂ) (τ : ℂ) := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id (τ : ℂ)).const_mul (γ 1 0 : ℂ)).add_const (γ 1 1 : ℂ)
  have hLf' : DifferentiableAt ℂ (modularLogDeriv f)
      ((γ • ofComplex (τ : ℂ) : ℍ) : ℂ) := by
    simpa only [ofComplex_apply] using hLf
  have hlhs := hLf'.hasDerivAt.comp (τ : ℂ) (hasDerivAt_SL2_smul_ofComplex γ τ.im_pos)
  simp only [ofComplex_apply] at hlhs
  have hrhs := ((hJ.pow 2).mul hLg.hasDerivAt).add
    ((hJ.const_mul (2 * (γ 1 0 : ℂ))).div_const (2 * π * I))
  have he : (fun z : ℂ => modularLogDeriv f ((γ • ofComplex z : ℍ) : ℂ)) =ᶠ[𝓝 (τ : ℂ)]
      (fun z : ℂ => ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ^ 2 * modularLogDeriv g z +
        2 * (γ 1 0 : ℂ) * ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) / (2 * π * I)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos]
      with z hz
    simpa only [ofComplex_apply_of_im_pos hz, UpperHalfPlane.coe_mk] using
      modularLogDeriv_weightTwo_relation hf hg hg0 γ hrel ⟨z, hz⟩
  have hdEq := hlhs.deriv.symm.trans (he.deriv_eq.trans hrhs.deriv)
  norm_num only [Nat.cast_ofNat, pow_one, one_div] at hdEq
  change deriv (modularLogDeriv f) ((γ • τ : ℍ) : ℂ) * (j ^ 2)⁻¹ =
    2 * j * (γ 1 0 : ℂ) * modularLogDeriv g τ + j ^ 2 * deriv (modularLogDeriv g) τ +
      (2 * (γ 1 0 : ℂ) * (γ 1 0 : ℂ)) / (2 * π * I) at hdEq
  have hdEq' := (mul_inv_eq_iff_eq_mul₀ (pow_ne_zero 2 hj)).mp hdEq
  rw [hdEq']
  dsimp only [j]
  ring

theorem modularLogDerivCorrection_slash_of_weightTwoRelation {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | 0 < z.im})
    (hg : DifferentiableOn ℂ g {z | 0 < z.im})
    (hf0 : ∀ z : ℂ, 0 < z.im → f z ≠ 0)
    (hg0 : ∀ z : ℂ, 0 < z.im → g z ≠ 0) (γ : SL(2, ℤ))
    (hrel : ∀ τ : ℍ, f ((γ • τ : ℍ) : ℂ) =
      ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ 2 * g τ) :
    (fun τ : ℍ => modularLogDerivCorrection f τ) ∣[(4 : ℤ)] γ =
      fun τ : ℍ => modularLogDerivCorrection g τ := by
  ext τ
  have hj : ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ≠ 0 := denom_ne_zero γ τ
  have hd : (2 * π * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  simp only [ModularForm.SL_slash_def, UpperHalfPlane.denom,
    zpow_neg, zpow_ofNat, modularLogDerivCorrection]
  change (modularLogDeriv f ((γ • τ : ℍ) : ℂ) ^ 2 -
    2 * deriv (modularLogDeriv f) ((γ • τ : ℍ) : ℂ) / (2 * π * I)) *
      (((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ 4)⁻¹ = _
  rw [modularLogDeriv_weightTwo_relation hf hg hg0 γ hrel τ,
    deriv_modularLogDeriv_weightTwo_relation hf hg hf0 hg0 γ hrel τ]
  field_simp [hj, hd]
  ring

end DirichletL

import Mathlib

/-!
Compact cutoffs in Mathlib's Schwartz space, supporting the Wiener-Ikehara
argument used for CDT v2 Section 2.2 (supplied TeX 3291-3310).
The approximation strategy is described in PNT+ Wiener.lean at revision
0766218b21b11ddf24103352ece7f0cb730945e0, lines 1080-1105 and 1545-1636;
The construction and derivative proofs here use canonical Mathlib APIs.
-/

namespace DirichletL

open MeasureTheory Filter Set
open scoped Topology SchwartzMap ContDiff

/-- Package a smooth compactly supported complex function in the canonical Schwartz space. -/
noncomputable def schwartzMapOfHasCompactSupport (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) : 𝓢(ℝ, ℂ) where
  toFun := f
  smooth' := hf
  decay' := by
    intro k n
    have hc : Continuous (fun x : ℝ => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
      (continuous_norm.pow k).mul (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
    obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support (hs.iteratedFDeriv n).norm.mul_left
    exact ⟨C, fun x => (Real.le_norm_self _).trans (hC x)⟩

/-- Multiply a Schwartz function by a compactly supported cutoff at a nonzero scale. -/
noncomputable def schwartzCutoff (ψ χ : 𝓢(ℝ, ℂ)) (hχ : HasCompactSupport (χ : ℝ → ℂ))
    (a : ℝ) (ha : a ≠ 0) : 𝓢(ℝ, ℂ) :=
  schwartzMapOfHasCompactSupport (fun t => ψ t * χ (t / a))
    (ψ.smooth'.mul (χ.smooth'.comp (contDiff_id.div_const a)))
    (by
      have hc := hχ.comp_homeomorph (Homeomorph.mulRight₀ a ha).symm
      simpa only [Function.comp_def, Homeomorph.mulRight₀_symm_apply, ← div_eq_mul_inv]
        using hc.mul_left (f := (ψ : ℝ → ℂ)))

theorem hasCompactSupport_schwartzCutoff (ψ χ : 𝓢(ℝ, ℂ))
    (hχ : HasCompactSupport (χ : ℝ → ℂ)) (a : ℝ) (ha : a ≠ 0) :
    HasCompactSupport (schwartzCutoff ψ χ hχ a ha : ℝ → ℂ) := by
  have hc := hχ.comp_homeomorph (Homeomorph.mulRight₀ a ha).symm
  simpa only [schwartzCutoff, schwartzMapOfHasCompactSupport, Function.comp_def,
    Homeomorph.mulRight₀_symm_apply, ← div_eq_mul_inv] using hc.mul_left (f := (ψ : ℝ → ℂ))

theorem deriv_schwartzCutoff (ψ χ : 𝓢(ℝ, ℂ)) (hχ : HasCompactSupport (χ : ℝ → ℂ))
    (a : ℝ) (ha : a ≠ 0) (t : ℝ) :
    SchwartzMap.derivCLM ℂ (schwartzCutoff ψ χ hχ a ha) t =
      SchwartzMap.derivCLM ℂ ψ t * χ (t / a) +
        ψ t * ((a : ℂ)⁻¹ * SchwartzMap.derivCLM ℂ χ (t / a)) := by
  have hdχ := χ.differentiableAt.hasDerivAt.scomp t ((hasDerivAt_id t).div_const a)
  simpa only [SchwartzMap.derivCLM_apply, schwartzCutoff, schwartzMapOfHasCompactSupport,
    Function.comp_def, id_eq, one_div, Complex.real_smul, Complex.ofReal_inv] using
    (ψ.differentiableAt.hasDerivAt.mul hdχ).deriv

theorem deriv_deriv_schwartzCutoff (ψ χ : 𝓢(ℝ, ℂ))
    (hχ : HasCompactSupport (χ : ℝ → ℂ)) (a : ℝ) (ha : a ≠ 0) (t : ℝ) :
    SchwartzMap.derivCLM ℂ (SchwartzMap.derivCLM ℂ (schwartzCutoff ψ χ hχ a ha)) t =
      SchwartzMap.derivCLM ℂ (SchwartzMap.derivCLM ℂ ψ) t * χ (t / a) +
        2 * (a : ℂ)⁻¹ * SchwartzMap.derivCLM ℂ ψ t * SchwartzMap.derivCLM ℂ χ (t / a) +
        ((a : ℂ)⁻¹) ^ 2 * ψ t * SchwartzMap.derivCLM ℂ (SchwartzMap.derivCLM ℂ χ) (t / a) := by
  change deriv (fun u => SchwartzMap.derivCLM ℂ (schwartzCutoff ψ χ hχ a ha) u) t = _
  simp_rw [deriv_schwartzCutoff]
  have hdχ := χ.differentiableAt.hasDerivAt.scomp t ((hasDerivAt_id t).div_const a)
  have hdχ' := (SchwartzMap.derivCLM ℂ χ).differentiableAt.hasDerivAt.scomp t
    ((hasDerivAt_id t).div_const a)
  have hd := ((SchwartzMap.derivCLM ℂ ψ).differentiableAt.hasDerivAt.mul hdχ).add
    (ψ.differentiableAt.hasDerivAt.mul (hdχ'.const_mul (a : ℂ)⁻¹))
  convert hd.deriv using 1
  simp only [SchwartzMap.derivCLM_apply, Function.comp_def, id_eq, one_div,
    Complex.real_smul, Complex.ofReal_inv]
  ring

end DirichletL

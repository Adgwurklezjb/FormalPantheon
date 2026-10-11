import Analysis.RationalFunctionCalculus
import Analysis.MobiusAnalyticInvolution

/-!
Rational and punctured-germ substitution for CDT v2, Lemma `etalecover`,
equation `y in x`, and the first coordinate reduction in Lemma `seven`.
-/

namespace DirichletL

open Polynomial Filter
open scoped Topology

/-- The involution of CDT equation `involutionfirst`, in the rational function field. -/
noncomputable def ratFuncMobiusInvolution : RatFunc ℂ :=
  RatFunc.X / (RatFunc.X - 1)

/-- The invariant rational coordinate of CDT equation `y in x`. -/
noncomputable def ratFuncMobiusCoordinate : RatFunc ℂ :=
  RatFunc.X + ratFuncMobiusInvolution

private theorem ratFuncX_sub_one_ne_zero : (RatFunc.X : RatFunc ℂ) - 1 ≠ 0 := by
  have h : (X - 1 : ℂ[X]) ≠ 0 := by
    intro h
    have hc := congrArg (fun p : ℂ[X] => p.coeff 1) h
    norm_num [coeff_one] at hc
  simpa only [map_sub, RatFunc.algebraMap_X, map_one] using RatFunc.algebraMap_ne_zero h

theorem ratFuncMobiusInvolution_ne_zero : ratFuncMobiusInvolution ≠ 0 :=
  div_ne_zero RatFunc.X_ne_zero ratFuncX_sub_one_ne_zero

theorem ratFuncMobiusDifference_ne_zero : RatFunc.X - ratFuncMobiusInvolution ≠ 0 := by
  intro h
  have he : (RatFunc.X : RatFunc ℂ) = RatFunc.X * (RatFunc.X - 1) :=
    (div_eq_iff ratFuncX_sub_one_ne_zero).mp (sub_eq_zero.mp h).symm
  have hp : (X : ℂ[X]) = X * (X - 1) :=
    RatFunc.algebraMap_injective ℂ (by
      simpa only [map_mul, map_sub, map_one, RatFunc.algebraMap_X] using he)
  have hc := congrArg (fun p : ℂ[X] => p.coeff 2) hp
  norm_num [mul_sub, coeff_X_pow, coeff_X] at hc

theorem ratFuncMobiusCoordinate_eq :
    ratFuncMobiusCoordinate = RatFunc.X ^ 2 / (RatFunc.X - 1) := by
  dsimp [ratFuncMobiusCoordinate, ratFuncMobiusInvolution]
  field_simp [ratFuncX_sub_one_ne_zero]
  ring

theorem ratFuncMobiusCoordinate_ne_constant (a : ℂ) :
    ratFuncMobiusCoordinate ≠ algebraMap ℂ (RatFunc ℂ) a := by
  intro h
  rw [ratFuncMobiusCoordinate_eq, div_eq_iff ratFuncX_sub_one_ne_zero] at h
  have hp : (X : ℂ[X]) ^ 2 = C a * (X - 1) :=
    RatFunc.algebraMap_injective ℂ (by
      simpa only [map_pow, map_mul, map_sub, map_one, RatFunc.algebraMap_X,
        RatFunc.algebraMap_C, RatFunc.C] using h)
  have hc := congrArg (fun p : ℂ[X] => p.coeff 2) hp
  norm_num [coeff_C_mul, coeff_X, coeff_one] at hc

theorem transcendental_ratFuncMobiusCoordinate : Transcendental ℂ ratFuncMobiusCoordinate := by
  intro h
  obtain ⟨a, ha⟩ := minpoly.mem_range_of_degree_eq_one ℂ ratFuncMobiusCoordinate
    (IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible h.isIntegral))
  exact ratFuncMobiusCoordinate_ne_constant a ha.symm

theorem aeval_ratFuncMobiusCoordinate_injective :
    Function.Injective (aeval ratFuncMobiusCoordinate : ℂ[X] →ₐ[ℂ] RatFunc ℂ) :=
  transcendental_iff_injective.mp transcendental_ratFuncMobiusCoordinate

theorem mobiusCoordinate_eq_sq_div {z : ℂ} (hz : z ≠ 1) :
    mobiusCoordinate z = z ^ 2 / (z - 1) := by
  dsimp [mobiusCoordinate]
  field_simp [sub_ne_zero.mpr hz]
  ring

theorem tendsto_mobiusCoordinate_zero : Tendsto mobiusCoordinate (𝓝 0) (𝓝 0) := by
  simpa only [mobiusCoordinate, zero_div, zero_add] using
    (analyticAt_mobiusCoordinate (by norm_num : (0 : ℂ) ≠ 1)).continuousAt.tendsto

theorem tendsto_mobiusCoordinate_punctured_zero :
    Tendsto mobiusCoordinate (𝓝[≠] 0) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_mobiusCoordinate_zero.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [(eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ 1)).filter_mono
    nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hz0
  change mobiusCoordinate z ≠ 0
  rw [mobiusCoordinate_eq_sq_div hz]
  exact div_ne_zero (pow_ne_zero 2 hz0) (sub_ne_zero.mpr hz)

theorem ratFuncEvalGerm_polynomial (p : ℂ[X]) (w : ℂ) :
    ratFuncEvalGerm w (algebraMap ℂ[X] (RatFunc ℂ) p) =
      (fun z => p.eval z : ℂ → ℂ) := by
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall (fun z => by simp only [RatFunc.eval_algebraMap, Algebra.algebraMap_self_apply, Polynomial.eval₂_id])

theorem ratFuncEvalGerm_X : ratFuncEvalGerm 0 RatFunc.X = (fun z : ℂ => z : ℂ → ℂ) := by
  simpa only [RatFunc.algebraMap_X, eval_X] using ratFuncEvalGerm_polynomial X 0

theorem ratFuncEvalGerm_mobiusInvolution :
    ratFuncEvalGerm 0 ratFuncMobiusInvolution =
      (mobiusAnalyticInvolution : Germ (𝓝[≠] (0 : ℂ)) ℂ) := by
  have h : (X - 1 : ℂ[X]) ≠ 0 := by
    intro h
    have hc := congrArg (fun p : ℂ[X] => p.coeff 1) h
    norm_num [coeff_one] at hc
  simpa only [map_sub, map_one, RatFunc.algebraMap_X, eval_X, eval_sub, eval_one,
    ratFuncMobiusInvolution, mobiusAnalyticInvolution] using
    ratFuncEvalGerm_polynomial_div X h 0

theorem ratFuncEvalGerm_mobiusCoordinate :
    ratFuncEvalGerm 0 ratFuncMobiusCoordinate =
      (mobiusCoordinate : Germ (𝓝[≠] (0 : ℂ)) ℂ) := by
  rw [ratFuncMobiusCoordinate, map_add, ratFuncEvalGerm_X, ratFuncEvalGerm_mobiusInvolution]
  rfl

theorem ratFuncEvalGerm_aeval_mobiusCoordinate (p : ℂ[X]) :
    ratFuncEvalGerm 0 (aeval ratFuncMobiusCoordinate p) =
      (fun z => p.eval (mobiusCoordinate z) : ℂ → ℂ) := by
  have hC (a : ℂ) : ratFuncEvalGerm 0 (algebraMap ℂ (RatFunc ℂ) a) =
      (fun _ : ℂ => a : ℂ → ℂ) := by
    simpa only [RatFunc.algebraMap_C, RatFunc.C, eval_C] using
      ratFuncEvalGerm_polynomial (C a) 0
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq]
      simp only [eval_add]
      rfl
  | monomial n a =>
      rw [aeval_monomial, map_mul, map_pow, hC, ratFuncEvalGerm_mobiusCoordinate]
      simp only [eval_monomial]
      rfl

end DirichletL

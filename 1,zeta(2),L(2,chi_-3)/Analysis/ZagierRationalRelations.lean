import Analysis.ZagierRelationContinuation
import Analysis.RationalFunctionCalculus

/-!
Clearing rational differential relations in CDT v2, Lemma `14functions`,
between equations `todiff` and `remaining`. The derivative-independence
criterion keeps monodromy irreducibility as an explicit input, supplied at
interval bases by `ZagierDerivativeIndependence`.
-/

namespace DirichletL

open Polynomial Filter
open scoped Topology

theorem zagierPolynomialResidual_eq_ratFunc_mul (B : Fin 4 → RatFunc ℂ)
    (Q : ℂ[X]) (P : Fin 4 → ℂ[X])
    (hrep : ∀ i, algebraMap ℂ[X] (RatFunc ℂ) (P i) =
      algebraMap ℂ[X] (RatFunc ℂ) Q * B i)
    (f : ℂ → ℂ) {z : ℂ} (hden : ∀ i, (B i).denom.eval z ≠ 0) :
    zagierPolynomialResidual P f z =
      Q.eval z * ∑ i, (B i).eval (RingHom.id ℂ) z * zagierODEState f z i := by
  rw [zagierPolynomialResidual, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he := congrArg (RatFunc.eval (RingHom.id ℂ) z) (hrep i)
  rw [RatFunc.eval_mul (RingHom.id ℂ) z (x := algebraMap ℂ[X] (RatFunc ℂ) Q)
    (y := B i) (by simp) (by simpa using hden i)] at he
  have hi : (P i).eval z = Q.eval z * (B i).eval (RingHom.id ℂ) z := by simpa using he
  rw [hi]
  ring

/-- Clearing a punctured rational relation gives a full analytic polynomial residual germ. -/
theorem zagierPolynomialResidual_eventuallyEq_zero_of_ratFunc (B : Fin 4 → RatFunc ℂ)
    (Q : ℂ[X]) (P : Fin 4 → ℂ[X])
    (hrep : ∀ i, algebraMap ℂ[X] (RatFunc ℂ) (P i) =
      algebraMap ℂ[X] (RatFunc ℂ) Q * B i)
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hrel : ∀ᶠ w in 𝓝[≠] z,
      ∑ i, (B i).eval (RingHom.id ℂ) w * zagierODEState f w i = 0) :
    zagierPolynomialResidual P f =ᶠ[𝓝 z] 0 := by
  have ha := analyticOnNhd_zagierPolynomialResidual P
    (show AnalyticOnNhd ℂ f {x | AnalyticAt ℂ f x} from fun _ hx => hx) z hf
  apply ha.frequently_zero_iff_eventually_zero.mp
  apply Filter.Eventually.frequently
  filter_upwards [hrel, eventually_all.mpr
    (fun i : Fin 4 => eventually_ne_zero_polynomial_eval (B i).denom_ne_zero z)] with w hw hd
  rw [zagierPolynomialResidual_eq_ratFunc_mul B Q P hrep f hd, hw, mul_zero]

theorem eq_zero_of_zagierRelation_denominator (B : Fin 4 → RatFunc ℂ)
    {Q : ℂ[X]} (hQ : Q ≠ 0) {P : Fin 4 → ℂ[X]}
    (hrep : ∀ i, algebraMap ℂ[X] (RatFunc ℂ) (P i) =
      algebraMap ℂ[X] (RatFunc ℂ) Q * B i) (hP : P = 0) : B = 0 := by
  funext i
  have hi : algebraMap ℂ[X] (RatFunc ℂ) Q * B i = 0 := by
    simpa only [hP, Pi.zero_apply, map_zero] using (hrep i).symm
  exact (mul_eq_zero.mp hi).resolve_left (RatFunc.algebraMap_ne_zero hQ)

theorem zagierPolynomialResidual_eventuallyEq_zero_iff_ratFunc (B : Fin 4 → RatFunc ℂ)
    {Q : ℂ[X]} (hQ : Q ≠ 0) (P : Fin 4 → ℂ[X])
    (hrep : ∀ i, algebraMap ℂ[X] (RatFunc ℂ) (P i) =
      algebraMap ℂ[X] (RatFunc ℂ) Q * B i)
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    zagierPolynomialResidual P f =ᶠ[𝓝 z] 0 ↔
      ∀ᶠ w in 𝓝[≠] z, ∑ i, (B i).eval (RingHom.id ℂ) w * zagierODEState f w i = 0 := by
  constructor
  · intro h
    filter_upwards [h.filter_mono nhdsWithin_le_nhds,
      eventually_ne_zero_polynomial_eval hQ z, eventually_all.mpr
      (fun i : Fin 4 => eventually_ne_zero_polynomial_eval (B i).denom_ne_zero z)] with w hw hqw hd
    rw [zagierPolynomialResidual_eq_ratFunc_mul B Q P hrep f hd] at hw
    exact (mul_eq_zero.mp hw).resolve_left hqw
  · exact zagierPolynomialResidual_eventuallyEq_zero_of_ratFunc B Q P hrep hf

/-- Actual monodromy preserves rational differential relations, including base-point poles. -/
theorem zagierRatFuncRelation_monodromy_iff (b : zagierODERegularSet)
    (B : Fin 4 → RatFunc ℂ) (g : FundamentalGroup zagierODERegularSet b)
    (φ : zagierSolutionGerms (b : ℂ)) {f₀ f₁ : ℂ → ℂ}
    (h₀ : (φ : Germ (𝓝 (b : ℂ)) ℂ) = f₀)
    (h₁ : (zagierMonodromyRepresentation b g φ : Germ (𝓝 (b : ℂ)) ℂ) = f₁) :
    (∀ᶠ z in 𝓝[≠] (b : ℂ),
      ∑ i, (B i).eval (RingHom.id ℂ) z * zagierODEState f₁ z i = 0) ↔
    (∀ᶠ z in 𝓝[≠] (b : ℂ),
      ∑ i, (B i).eval (RingHom.id ℂ) z * zagierODEState f₀ z i = 0) := by
  have ha {ψ : zagierSolutionGerms (b : ℂ)} {f : ℂ → ℂ}
      (hψ : (ψ : Germ (𝓝 (b : ℂ)) ℂ) = f) : AnalyticAt ℂ f (b : ℂ) := by
    have hm : (f : Germ (𝓝 (b : ℂ)) ℂ) ∈ zagierSolutionGerms (b : ℂ) := by
      rw [← hψ]
      exact ψ.property
    exact (mem_zagierSolutionGerms_iff.mp hm).1
  obtain ⟨Q, hQ, P, hP⟩ := exists_ratFunc_denominator B
  rw [← zagierPolynomialResidual_eventuallyEq_zero_iff_ratFunc B hQ P hP (ha h₁),
    ← zagierPolynomialResidual_eventuallyEq_zero_iff_ratFunc B hQ P hP (ha h₀),
    ← mem_zagierPolynomialRelationSubmodule_iff P _ h₁,
    ← mem_zagierPolynomialRelationSubmodule_iff P _ h₀]
  exact zagierMonodromy_mem_polynomialRelation_iff b P g φ

/-- Irreducibility excludes rational relations on any nonzero actual solution germ. -/
theorem eq_zero_of_zagierRatFuncRelation_of_isSimpleOrder (b : zagierODERegularSet)
    (hI : IsSimpleOrder (zagierMonodromyRepresentation b).invtSubmodule)
    (B : Fin 4 → RatFunc ℂ) {φ : zagierSolutionGerms (b : ℂ)} (hφ : φ ≠ 0)
    {f : ℂ → ℂ} (hrep : (φ : Germ (𝓝 (b : ℂ)) ℂ) = f)
    (hrel : ∀ᶠ z in 𝓝[≠] (b : ℂ),
      ∑ i, (B i).eval (RingHom.id ℂ) z * zagierODEState f z i = 0) : B = 0 := by
  have hm : (f : Germ (𝓝 (b : ℂ)) ℂ) ∈ zagierSolutionGerms (b : ℂ) := by
    rw [← hrep]
    exact φ.property
  have hf := (mem_zagierSolutionGerms_iff.mp hm).1
  obtain ⟨Q, hQ, P, hP⟩ := exists_ratFunc_denominator B
  have hr := zagierPolynomialResidual_eventuallyEq_zero_of_ratFunc B Q P hP hf hrel
  have hp0 := eq_zero_of_zagierPolynomialRelation_of_isSimpleOrder b P hI hφ
    ((mem_zagierPolynomialRelationSubmodule_iff P φ hrep).mpr hr)
  exact eq_zero_of_zagierRelation_denominator B hQ hP hp0

/-- The C(y)-coefficient criterion for actual G_A, conditional on monodromy irreducibility. -/
theorem eq_zero_of_zagierRatFuncRelation_hA_of_isSimpleOrder (b : zagierODERegularSet)
    (hb : ‖(b : ℂ)‖ < 1 / 648)
    (hI : IsSimpleOrder (zagierMonodromyRepresentation b).invtSubmodule)
    (B : Fin 4 → RatFunc ℂ)
    (hrel : ∀ᶠ z in 𝓝[≠] (b : ℂ),
      ∑ i, (B i).eval (RingHom.id ℂ) z * zagierODEState (symmetrizedAnalytic hA) z i = 0) :
    B = 0 :=
  eq_zero_of_zagierRatFuncRelation_of_isSimpleOrder b hI B
    (zagierPrincipalSolutionGerm_ne_zero b hb) (zagierPrincipalSolutionGerm_coe b hb) hrel

end DirichletL

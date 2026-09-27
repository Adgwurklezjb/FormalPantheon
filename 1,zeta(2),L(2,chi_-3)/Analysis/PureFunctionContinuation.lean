import Analysis.AnalyticLinearODEHomotopy
import Analysis.PureFunctionCompanion

/-!
Continuation of CDT's literal seven pure functions on C minus {0,4}.
Loops homotopic to the constant loop preserve full germs, including the
normalized primitive constants in `defB67`, as required in `14functions`.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

theorem exists_analyticContinuationAlong_pureSeven :
    ∃ R : ℝ, 0 < R ∧ ∀ γ : C(unitInterval, pureRegularSet), ‖(γ 0 : ℂ)‖ < R →
      ∃ F : unitInterval → ℂ → Fin 7 → ℂ,
        (∀ i, AnalyticContinuationAlong (fun t => (γ t : ℂ)) (fun t z => F t z i)) ∧
        F 0 =ᶠ[𝓝 (γ 0 : ℂ)] pureSevenState ∧
        ∀ t, ∀ᶠ z in 𝓝 (γ t : ℂ), HasDerivAt (F t) (pureSevenMatrix z *ᵥ F t z) z := by
  obtain ⟨R, hR, hinit⟩ := exists_pureSeven_initial_radius
  refine ⟨R, hR, ?_⟩
  intro γ hγ
  obtain ⟨ha, ho⟩ := hinit (γ 0 : ℂ) hγ
  have hz0 := ((mem_pureRegularSet_iff _).mp (γ 0).property).1
  exact pureSevenSystem.exists_analyticContinuationAlong γ pureSevenState ha (ho hz0).2

theorem exists_analyticContinuationAlong_pureSeven_homotopic_refl :
    ∃ R : ℝ, 0 < R ∧ ∀ x : pureRegularSet, ‖(x : ℂ)‖ < R → ∀ γ : Path x x,
      γ.Homotopic (Path.refl x) → ∃ F : unitInterval → ℂ → Fin 7 → ℂ,
        (∀ i, AnalyticContinuationAlong (fun t => (γ t : ℂ)) (fun t z => F t z i)) ∧
        F 0 =ᶠ[𝓝 (x : ℂ)] pureSevenState ∧ F 1 =ᶠ[𝓝 (x : ℂ)] pureSevenState ∧
        ∀ t, ∀ᶠ z in 𝓝 (γ t : ℂ), HasDerivAt (F t) (pureSevenMatrix z *ᵥ F t z) z := by
  obtain ⟨R, hR, hinit⟩ := exists_pureSeven_initial_radius
  refine ⟨R, hR, ?_⟩
  intro x hx γ hγ
  obtain ⟨ha, ho⟩ := hinit (x : ℂ) hx
  have hx0 := ((mem_pureRegularSet_iff _).mp x.property).1
  exact pureSevenSystem.exists_analyticContinuationAlong_homotopic_refl γ hγ pureSevenState ha
    (ho hx0).2

theorem pureSeven_continuation_end_eq_of_homotopic_refl :
    ∃ R : ℝ, 0 < R ∧ ∀ x : pureRegularSet, ‖(x : ℂ)‖ < R → ∀ γ : Path x x,
      γ.Homotopic (Path.refl x) → ∀ F : unitInterval → ℂ → Fin 7 → ℂ,
        (∀ i, AnalyticContinuationAlong (fun t => (γ t : ℂ)) (fun t z => F t z i)) →
        F 0 =ᶠ[𝓝 (x : ℂ)] pureSevenState → F 1 =ᶠ[𝓝 (x : ℂ)] pureSevenState := by
  obtain ⟨R, hR, hinit⟩ := exists_pureSeven_initial_radius
  refine ⟨R, hR, ?_⟩
  intro x hx γ hγ F hF hF0
  obtain ⟨ha, ho⟩ := hinit (x : ℂ) hx
  have hx0 := ((mem_pureRegularSet_iff _).mp x.property).1
  exact pureSevenSystem.analyticContinuationAlong_end_eq_of_homotopic_refl γ hγ ha (ho hx0).2 hF hF0

end DirichletL

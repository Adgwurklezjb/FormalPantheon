import Analysis.AnalyticContinuation

/-!
An invariant line for a nontrivial shear continuation is the fixed line.
This supplies the elementary local linear algebra for CDT v2, `14functions`.
-/

namespace DirichletL

open Filter unitInterval
open scoped Topology

theorem eq_zero_coefficient_of_linear_shear {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) {u v : V} {k : ℂ} (hu : T u = u) (hv : T v = v + k • u)
    (hk : k ≠ 0) (hind : ∀ a b : ℂ, a • u + b • v = 0 → a = 0 ∧ b = 0)
    {a b c : ℂ} (he : T (a • u + b • v) = c • (a • u + b • v)) : b = 0 := by
  have hrel : (a + b * k - c * a) • u + (b - c * b) • v = 0 := by
    calc
      _ = T (a • u + b • v) - c • (a • u + b • v) := by
        rw [map_add, map_smul, map_smul, hu, hv]
        simp only [add_smul, sub_smul, mul_smul, smul_add]
        abel
      _ = 0 := sub_eq_zero.mpr he
  obtain ⟨hu', hv'⟩ := hind _ _ hrel
  by_contra hb
  have hc : c = 1 := by
    have hprod : (1 - c) * b = 0 := by linear_combination hv'
    have h := (mul_eq_zero.mp hprod).resolve_right hb
    linear_combination -h
  rw [hc] at hu'
  exact mul_ne_zero hb hk (by linear_combination hu')

theorem eq_zero_coefficient_of_analyticContinuation_shear {p : ℂ} {γ : Path p p}
    {U V : ℂ → ℂ} {v : I → ℂ → ℂ} {k : ℂ}
    (hU : AnalyticContinuationAlong γ (fun _ => U)) (hv : AnalyticContinuationAlong γ v)
    (hv₀ : v 0 =ᶠ[𝓝 p] V) (hv₁ : v 1 =ᶠ[𝓝 p] fun z => V z + k * U z) (hk : k ≠ 0)
    (hind : ∀ a b : ℂ, (fun z => a * U z + b * V z) =ᶠ[𝓝 p] 0 → a = 0 ∧ b = 0)
    {a b c : ℂ} {g : I → ℂ → ℂ} (hg : AnalyticContinuationAlong γ g)
    (hg₀ : g 0 =ᶠ[𝓝 p] fun z => a * U z + b * V z)
    (hg₁ : g 1 =ᶠ[𝓝 p] fun z => c * (a * U z + b * V z)) : b = 0 := by
  have ha : AnalyticContinuationAlong γ (fun _ _ => a) :=
    AnalyticContinuationAlong.const γ.continuous (fun _ => analyticAt_const)
  have hb : AnalyticContinuationAlong γ (fun _ _ => b) :=
    AnalyticContinuationAlong.const γ.continuous (fun _ => analyticAt_const)
  have hc : AnalyticContinuationAlong γ (fun t z => a * U z + b * v t z) :=
    (ha.mul hU).add (hb.mul hv)
  have hi : g 0 =ᶠ[𝓝 (γ 0)] fun z => a * U z + b * v 0 z := by
    simp only [Path.source]
    filter_upwards [hg₀, hv₀] with z hzg hzv
    rw [hzg, hzv]
  have he := hg.eq_of_preconnectedSpace hc hi 1
  simp only [Path.target] at he
  have hrel : (fun z => (a + b * k - c * a) * U z + (b - c * b) * V z) =ᶠ[𝓝 p] 0 := by
    filter_upwards [he, hg₁, hv₁] with z hz hzg hzv
    dsimp at hz hzg hzv ⊢
    rw [hz, hzv] at hzg
    linear_combination hzg
  obtain ⟨hu, hv⟩ := hind _ _ hrel
  by_contra hb₀
  have hc₁ : c = 1 := by
    have hprod : (1 - c) * b = 0 := by linear_combination hv
    have h := (mul_eq_zero.mp hprod).resolve_right hb₀
    linear_combination -h
  rw [hc₁] at hu
  exact mul_ne_zero hb₀ hk (by linear_combination hu)

end DirichletL

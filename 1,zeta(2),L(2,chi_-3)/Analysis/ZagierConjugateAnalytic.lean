import Analysis.AnalyticSecondOrderODE
import Analysis.ZagierPullbackAnalytic

/-!
The analytic Mobius-conjugate summand of CDT v2's fourth-order equation.
The coefficients and common-multiple certificate are recorded with `explicitode`.
-/

namespace DirichletL

open Filter
open scoped Topology

theorem eventuallyEq_zagierSecondOrderODE {f g : ℂ → ℂ} {z : ℂ}
    (he : f =ᶠ[𝓝 z] g) : zagierSecondOrderODE f =ᶠ[𝓝 z] zagierSecondOrderODE g := by
  filter_upwards [he, he.deriv, he.deriv.deriv] with w h₀ h₁ h₂
  simp only [zagierSecondOrderODE, h₀, h₁, h₂]

/-- The analytic version of the formal conjugate second-order operator. -/
noncomputable def zagierConjugateAnalyticODE (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * (z - 1) ^ 2 * (8 * z + 1) * deriv (deriv f) z +
    (z - 1) * (8 * z ^ 2 - 16 * z - 1) * deriv f z + 3 * (2 * z + 1) * f z

theorem hasDerivAt_zagierConjugateAnalyticODE {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) :
    HasDerivAt (zagierConjugateAnalyticODE f)
      (z * (z - 1) ^ 2 * (8 * z + 1) * deriv (deriv (deriv f)) z +
        (40 * z ^ 3 - 69 * z ^ 2 + 27 * z + 2) * deriv (deriv f) z +
        (24 * z ^ 2 - 42 * z + 18) * deriv f z + 6 * f z) z := by
  have hA := ((hasDerivAt_id z).mul (((hasDerivAt_id z).sub_const 1).pow 2)).mul
    (((hasDerivAt_id z).const_mul 8).add_const 1)
  have hB := ((hasDerivAt_id z).sub_const 1).mul
    (((((hasDerivAt_id z).pow 2).const_mul 8).sub
      ((hasDerivAt_id z).const_mul 16)).sub_const 1)
  have hC := (((hasDerivAt_id z).const_mul 2).add_const 1).const_mul 3
  have h := ((hA.mul hf.deriv.deriv.differentiableAt.hasDerivAt).add
    (hB.mul hf.deriv.differentiableAt.hasDerivAt)).add (hC.mul hf.differentiableAt.hasDerivAt)
  convert h using 1
  dsimp [zagierConjugateAnalyticODE]
  ring

theorem hasDerivAt_deriv_zagierConjugateAnalyticODE {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) :
    HasDerivAt (deriv (zagierConjugateAnalyticODE f))
      (z * (z - 1) ^ 2 * (8 * z + 1) * deriv (deriv (deriv (deriv f))) z +
        (72 * z ^ 3 - 114 * z ^ 2 + 39 * z + 3) * deriv (deriv (deriv f)) z +
        (144 * z ^ 2 - 180 * z + 45) * deriv (deriv f) z +
        (48 * z - 36) * deriv f z) z := by
  have he : deriv (zagierConjugateAnalyticODE f) =ᶠ[𝓝 z] fun w =>
      w * (w - 1) ^ 2 * (8 * w + 1) * deriv (deriv (deriv f)) w +
        (40 * w ^ 3 - 69 * w ^ 2 + 27 * w + 2) * deriv (deriv f) w +
        (24 * w ^ 2 - 42 * w + 18) * deriv f w + 6 * f w := by
    filter_upwards [hf.eventually_analyticAt] with w hw
    exact (hasDerivAt_zagierConjugateAnalyticODE hw).deriv
  have hA := ((hasDerivAt_id z).mul (((hasDerivAt_id z).sub_const 1).pow 2)).mul
    (((hasDerivAt_id z).const_mul 8).add_const 1)
  have hB := (((((hasDerivAt_id z).pow 3).const_mul 40).sub
    (((hasDerivAt_id z).pow 2).const_mul 69)).add
      ((hasDerivAt_id z).const_mul 27)).add_const 2
  have hC := ((((hasDerivAt_id z).pow 2).const_mul 24).sub
    ((hasDerivAt_id z).const_mul 42)).add_const 18
  have h := (((hA.mul hf.deriv.deriv.deriv.differentiableAt.hasDerivAt).add
    (hB.mul hf.deriv.deriv.differentiableAt.hasDerivAt)).add
      (hC.mul hf.deriv.differentiableAt.hasDerivAt)).add
        (hf.differentiableAt.hasDerivAt.const_mul 6)
  convert h.congr_of_eventuallyEq he using 1
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

theorem eventually_zagierPullbackAnalyticODE_of_conjugate {f : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 1) (hf : AnalyticAt ℂ f z)
    (he : zagierConjugateAnalyticODE f =ᶠ[𝓝 z] 0) :
    zagierPullbackAnalyticODE f =ᶠ[𝓝 z] 0 := by
  filter_upwards [hf.eventually_analyticAt, he, he.deriv, he.deriv.deriv,
    eventually_ne_nhds hz] with w hw h₀ h₁ h₂ hw₁
  have hd₁ := (hasDerivAt_zagierConjugateAnalyticODE hw).deriv
  have hd₂ := (hasDerivAt_deriv_zagierConjugateAnalyticODE hw).deriv
  have he₁ : w * (w - 1) ^ 2 * (8 * w + 1) * deriv (deriv (deriv f)) w +
      (40 * w ^ 3 - 69 * w ^ 2 + 27 * w + 2) * deriv (deriv f) w +
      (24 * w ^ 2 - 42 * w + 18) * deriv f w + 6 * f w = 0 := by
    rw [← hd₁]
    simpa using h₁
  have he₂ : w * (w - 1) ^ 2 * (8 * w + 1) * deriv (deriv (deriv (deriv f))) w +
      (72 * w ^ 3 - 114 * w ^ 2 + 39 * w + 3) * deriv (deriv (deriv f)) w +
      (144 * w ^ 2 - 180 * w + 45) * deriv (deriv f) w +
      (48 * w - 36) * deriv f w = 0 := by
    rw [← hd₂]
    simpa using h₂
  have h : (w - 1) * zagierPullbackAnalyticODE f w = 0 := by
    rw [zagierPullbackAnalyticODE, zagierPullbackJet_conjugate]
    dsimp only [zagierConjugateAnalyticODE, Pi.zero_apply] at h₀
    rw [h₀, he₁, he₂]
    ring
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hw₁)

theorem zagierConjugateAnalyticODE_linearCombination {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (a b : ℂ) :
    zagierConjugateAnalyticODE (fun w => a * f w + b * g w) z =
      a * zagierConjugateAnalyticODE f z + b * zagierConjugateAnalyticODE g z := by
  have hd : deriv (fun w => a * f w + b * g w) =ᶠ[𝓝 z]
      fun w => a * deriv f w + b * deriv g w := by
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with w hwf hwg
    exact ((hwf.differentiableAt.hasDerivAt.const_mul a).fun_add
      (hwg.differentiableAt.hasDerivAt.const_mul b)).deriv
  have hdd := (hf.deriv.differentiableAt.hasDerivAt.const_mul a).fun_add
    (hg.deriv.differentiableAt.hasDerivAt.const_mul b)
  rw [zagierConjugateAnalyticODE, hd.deriv_eq, hdd.deriv, hd.self_of_nhds]
  dsimp [zagierConjugateAnalyticODE]
  ring

theorem eventuallyEq_zagierConjugateAnalyticODE {f g : ℂ → ℂ} {z : ℂ}
    (he : f =ᶠ[𝓝 z] g) :
    zagierConjugateAnalyticODE f =ᶠ[𝓝 z] zagierConjugateAnalyticODE g := by
  filter_upwards [he, he.deriv, he.deriv.deriv] with w h₀ h₁ h₂
  simp only [zagierConjugateAnalyticODE, h₀, h₁, h₂]

theorem exists_analytic_zagierSecondOrder_ode {z : ℂ}
    (hz : z * (1 - z) * (1 - 9 * z) ≠ 0) (u v : ℂ) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f z ∧ f z = u ∧ deriv f z = v ∧
      zagierSecondOrderODE f =ᶠ[𝓝 z] 0 :=
  exists_analytic_secondOrder_ode
    (a := fun w => w * (1 - w) * (1 - 9 * w))
    (b := fun w => 1 - 20 * w + 27 * w ^ 2) (c := fun w => 9 * w - 3)
    (by fun_prop) (by fun_prop) (by fun_prop) hz u v

theorem exists_analytic_zagierConjugate_ode {z : ℂ}
    (hz : z * (z - 1) ^ 2 * (8 * z + 1) ≠ 0) (u v : ℂ) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f z ∧ f z = u ∧ deriv f z = v ∧
      zagierConjugateAnalyticODE f =ᶠ[𝓝 z] 0 :=
  exists_analytic_secondOrder_ode
    (a := fun w => w * (w - 1) ^ 2 * (8 * w + 1))
    (b := fun w => (w - 1) * (8 * w ^ 2 - 16 * w - 1)) (c := fun w => 3 * (2 * w + 1))
    (by fun_prop) (by fun_prop) (by fun_prop) hz u v

end DirichletL

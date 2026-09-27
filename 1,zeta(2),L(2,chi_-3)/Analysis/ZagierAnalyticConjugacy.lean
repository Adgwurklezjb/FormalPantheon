import Analysis.MobiusAnalyticInvolution
import Analysis.ZagierConjugateAnalytic

/-!
Analytic exchange of the second-order equations under CDT v2's `involutionfirst`.
These exact residual identities connect `functionsH` to `14functions`.
-/

namespace DirichletL

open Filter
open scoped Topology

theorem zagierConjugateAnalyticODE_comp_mobiusAnalyticInvolution {f : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 1) (hf : AnalyticAt ℂ f (mobiusAnalyticInvolution z)) :
    zagierConjugateAnalyticODE (f ∘ mobiusAnalyticInvolution) z =
      (z - 1) * zagierSecondOrderODE f (mobiusAnalyticInvolution z) := by
  have hw := analyticAt_mobiusAnalyticInvolution hz
  have h₁ := (hf.differentiableAt.hasDerivAt.comp z
    (hasDerivAt_mobiusAnalyticInvolution hz)).deriv
  have h₂ := iteratedDeriv_comp_two hf.contDiffAt hw.contDiffAt
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, deriv_mobiusAnalyticInvolution hz,
    deriv_two_mobiusAnalyticInvolution hz] at h₂
  rw [zagierConjugateAnalyticODE, h₁, h₂]
  dsimp only [zagierSecondOrderODE, Function.comp_apply]
  generalize f (mobiusAnalyticInvolution z) = u
  generalize deriv f (mobiusAnalyticInvolution z) = v
  generalize deriv (deriv f) (mobiusAnalyticInvolution z) = a
  dsimp only [mobiusAnalyticInvolution]
  field_simp [sub_ne_zero.mpr hz]
  ring

theorem zagierSecondOrderODE_comp_mobiusAnalyticInvolution {f : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 1) (hf : AnalyticAt ℂ f (mobiusAnalyticInvolution z)) :
    zagierSecondOrderODE (f ∘ mobiusAnalyticInvolution) z =
      (z - 1) * zagierConjugateAnalyticODE f (mobiusAnalyticInvolution z) := by
  have hw := analyticAt_mobiusAnalyticInvolution hz
  have h₁ := (hf.differentiableAt.hasDerivAt.comp z
    (hasDerivAt_mobiusAnalyticInvolution hz)).deriv
  have h₂ := iteratedDeriv_comp_two hf.contDiffAt hw.contDiffAt
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, deriv_mobiusAnalyticInvolution hz,
    deriv_two_mobiusAnalyticInvolution hz] at h₂
  rw [zagierSecondOrderODE, h₁, h₂]
  dsimp only [zagierConjugateAnalyticODE, Function.comp_apply]
  generalize f (mobiusAnalyticInvolution z) = u
  generalize deriv f (mobiusAnalyticInvolution z) = v
  generalize deriv (deriv f) (mobiusAnalyticInvolution z) = a
  dsimp only [mobiusAnalyticInvolution]
  field_simp [sub_ne_zero.mpr hz]
  ring

theorem eventually_zagierConjugate_comp_mobiusAnalyticInvolution {f : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 1) (hf : AnalyticAt ℂ f (mobiusAnalyticInvolution z))
    (hE : zagierSecondOrderODE f =ᶠ[𝓝 (mobiusAnalyticInvolution z)] 0) :
    zagierConjugateAnalyticODE (f ∘ mobiusAnalyticInvolution) =ᶠ[𝓝 z] 0 := by
  have ht := (analyticAt_mobiusAnalyticInvolution hz).continuousAt.tendsto
  filter_upwards [eventually_ne_nhds hz, ht.eventually hf.eventually_analyticAt,
    ht.eventually hE] with w hw hwf he
  rw [zagierConjugateAnalyticODE_comp_mobiusAnalyticInvolution hw hwf, he]
  exact mul_zero _

theorem eventually_zagierSecondOrder_comp_mobiusAnalyticInvolution {f : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 1) (hf : AnalyticAt ℂ f (mobiusAnalyticInvolution z))
    (hC : zagierConjugateAnalyticODE f =ᶠ[𝓝 (mobiusAnalyticInvolution z)] 0) :
    zagierSecondOrderODE (f ∘ mobiusAnalyticInvolution) =ᶠ[𝓝 z] 0 := by
  have ht := (analyticAt_mobiusAnalyticInvolution hz).continuousAt.tendsto
  filter_upwards [eventually_ne_nhds hz, ht.eventually hf.eventually_analyticAt,
    ht.eventually hC] with w hw hwf he
  rw [zagierSecondOrderODE_comp_mobiusAnalyticInvolution hw hwf, he]
  exact mul_zero _

end DirichletL

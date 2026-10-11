import Analysis.MobiusAnalyticCoordinate
import Analysis.ZagierDescentAnalyticODE
import Analysis.ZagierEndpointSymmetry

/-!
Analytic interpretation of the polynomial pullback certificates for CDT v2
equations `zagr`, `y in x`, and `explicitode`. A local inverse transports
actual second-order solutions to fourth-order solution germs.
-/

namespace DirichletL

open Filter
open scoped Topology

/-- The fourth-order pullback residual evaluated on an ordinary analytic jet. -/
noncomputable def zagierPullbackAnalyticODE (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  zagierPullbackJet z (f z) (deriv f z) (deriv (deriv f) z)
    (deriv (deriv (deriv f)) z) (deriv (deriv (deriv (deriv f))) z)

theorem hasDerivAt_zagierSecondOrderODE {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) :
    HasDerivAt (zagierSecondOrderODE f)
      (z * (1 - z) * (1 - 9 * z) * deriv (deriv (deriv f)) z +
        2 * (1 - 20 * z + 27 * z ^ 2) * deriv (deriv f) z +
        (63 * z - 23) * deriv f z + 9 * f z) z := by
  have hA := ((hasDerivAt_id z).mul ((hasDerivAt_id z).const_sub 1)).mul
    (((hasDerivAt_id z).const_mul 9).const_sub 1)
  have hB := (((hasDerivAt_id z).const_mul 20).const_sub 1).add
    (((hasDerivAt_id z).pow 2).const_mul 27)
  have hC := ((hasDerivAt_id z).const_mul 9).sub_const 3
  have h := ((hA.mul hf.deriv.deriv.differentiableAt.hasDerivAt).add
    (hB.mul hf.deriv.differentiableAt.hasDerivAt)).add (hC.mul hf.differentiableAt.hasDerivAt)
  convert h using 1
  dsimp [zagierSecondOrderODE]
  ring

theorem hasDerivAt_deriv_zagierSecondOrderODE {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) :
    HasDerivAt (deriv (zagierSecondOrderODE f))
      (z * (1 - z) * (1 - 9 * z) * deriv (deriv (deriv (deriv f))) z +
        3 * (1 - 20 * z + 27 * z ^ 2) * deriv (deriv (deriv f)) z +
        (171 * z - 63) * deriv (deriv f) z + 72 * deriv f z) z := by
  have he : deriv (zagierSecondOrderODE f) =ᶠ[𝓝 z] fun w =>
      w * (1 - w) * (1 - 9 * w) * deriv (deriv (deriv f)) w +
        2 * (1 - 20 * w + 27 * w ^ 2) * deriv (deriv f) w +
        (63 * w - 23) * deriv f w + 9 * f w := by
    filter_upwards [hf.eventually_analyticAt] with w hw
    exact (hasDerivAt_zagierSecondOrderODE hw).deriv
  have hA := ((hasDerivAt_id z).mul ((hasDerivAt_id z).const_sub 1)).mul
    (((hasDerivAt_id z).const_mul 9).const_sub 1)
  have hB := (((hasDerivAt_id z).const_mul 20).const_sub 1).add
    (((hasDerivAt_id z).pow 2).const_mul 27)
  have hC := ((hasDerivAt_id z).const_mul 63).sub_const 23
  have h := (((hA.mul hf.deriv.deriv.deriv.differentiableAt.hasDerivAt).add
    ((hB.const_mul 2).mul hf.deriv.deriv.differentiableAt.hasDerivAt)).add
      (hC.mul hf.deriv.differentiableAt.hasDerivAt)).add
        (hf.differentiableAt.hasDerivAt.const_mul 9)
  convert h.congr_of_eventuallyEq he using 1
  simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat,
    Nat.reduceSub, pow_one]
  ring

theorem eventually_zagierPullbackAnalyticODE_of_secondOrder {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (he : zagierSecondOrderODE f =ᶠ[𝓝 z] 0) :
    zagierPullbackAnalyticODE f =ᶠ[𝓝 z] 0 := by
  filter_upwards [hf.eventually_analyticAt, he, he.deriv, he.deriv.deriv]
    with w hw h₀ h₁ h₂
  have hd₁ := (hasDerivAt_zagierSecondOrderODE hw).deriv
  have hd₂ := (hasDerivAt_deriv_zagierSecondOrderODE hw).deriv
  have he₁ : w * (1 - w) * (1 - 9 * w) * deriv (deriv (deriv f)) w +
      2 * (1 - 20 * w + 27 * w ^ 2) * deriv (deriv f) w +
      (63 * w - 23) * deriv f w + 9 * f w = 0 := by
    rw [← hd₁]
    simpa using h₁
  have he₂ : w * (1 - w) * (1 - 9 * w) * deriv (deriv (deriv (deriv f))) w +
      3 * (1 - 20 * w + 27 * w ^ 2) * deriv (deriv (deriv f)) w +
      (171 * w - 63) * deriv (deriv f) w + 72 * deriv f w = 0 := by
    rw [← hd₂]
    simpa using h₂
  have hA : w * (1 - 10 * w + 9 * w ^ 2) = w * (1 - w) * (1 - 9 * w) := by ring
  rw [zagierPullbackAnalyticODE, zagierPullbackJet_source, hA]
  change _ = (0 : ℂ)
  dsimp only [zagierSecondOrderODE, Pi.zero_apply] at h₀
  rw [h₀, he₁, he₂]
  ring

theorem eventuallyEq_zagierPullbackAnalyticODE {f g : ℂ → ℂ} {z : ℂ}
    (he : f =ᶠ[𝓝 z] g) :
    zagierPullbackAnalyticODE f =ᶠ[𝓝 z] zagierPullbackAnalyticODE g := by
  filter_upwards [he, he.deriv, he.deriv.deriv, he.deriv.deriv.deriv,
    he.deriv.deriv.deriv.deriv] with w h₀ h₁ h₂ h₃ h₄
  simp only [zagierPullbackAnalyticODE, h₀, h₁, h₂, h₃, h₄]

theorem zagierPullbackAnalyticODE_comp_mobiusCoordinate {g : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 1) (hg : AnalyticAt ℂ g (mobiusCoordinate z)) :
    zagierPullbackAnalyticODE (g ∘ mobiusCoordinate) z =
      (z - 1) ^ 3 * zagierAnalyticODE g (mobiusCoordinate z) := by
  have hy := analyticAt_mobiusCoordinate hz
  have h₁ := (hg.differentiableAt.hasDerivAt.comp z (hasDerivAt_mobiusCoordinate hz)).deriv
  have h₂ := iteratedDeriv_comp_two hg.contDiffAt hy.contDiffAt
  have h₃ := iteratedDeriv_comp_three hg.contDiffAt hy.contDiffAt
  have h₄ := deriv_four_comp_of_analyticAt hy hg
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, deriv_mobiusCoordinate hz,
    deriv_two_mobiusCoordinate hz, deriv_three_mobiusCoordinate hz,
    deriv_four_mobiusCoordinate hz] at h₂ h₃ h₄
  have h₃' : deriv (deriv (deriv (g ∘ mobiusCoordinate))) z =
      deriv (deriv (deriv g)) (mobiusCoordinate z) * (1 - (1 - z)⁻¹ ^ 2) ^ 3 +
        3 * deriv (deriv g) (mobiusCoordinate z) * (1 - (1 - z)⁻¹ ^ 2) *
          (-2 * (1 - z)⁻¹ ^ 3) +
        deriv g (mobiusCoordinate z) * (-6 * (1 - z)⁻¹ ^ 4) := by
    rw [h₃]
    ring
  have hu : (z - 1) * (1 - z)⁻¹ = -1 := by
    field_simp [sub_ne_zero.mpr hz.symm]
    ring
  have hY : z + (1 - (1 - z)⁻¹) = mobiusCoordinate z := by
    rw [mobiusCoordinate_eq hz]
    ring
  rw [zagierPullbackAnalyticODE, h₁, h₂, h₃', h₄]
  simpa only [Function.comp_apply, hY, aeval_zagierODECoeffQ, zagierAnalyticODE] using
    zagierPullbackJet_chain z (1 - z)⁻¹ (g (mobiusCoordinate z))
      (deriv g (mobiusCoordinate z)) (deriv (deriv g) (mobiusCoordinate z))
      (deriv (deriv (deriv g)) (mobiusCoordinate z))
      (deriv (deriv (deriv (deriv g))) (mobiusCoordinate z)) hu

theorem exists_zagierAnalyticODE_of_pullback {f : ℂ → ℂ} {x : ℂ}
    (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) (hx₂ : x ≠ 2)
    (hf : AnalyticAt ℂ f x) (he : zagierPullbackAnalyticODE f =ᶠ[𝓝 x] 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (mobiusCoordinate x) ∧
      zagierAnalyticODE g =ᶠ[𝓝 (mobiusCoordinate x)] 0 ∧
        (g ∘ mobiusCoordinate) =ᶠ[𝓝 x] f := by
  obtain ⟨v, hv, hvx, hleft, hright⟩ := exists_analyticAt_localInverse
    (analyticAt_mobiusCoordinate hx₁) (deriv_mobiusCoordinate_ne_zero hx₀ hx₁ hx₂)
  let g : ℂ → ℂ := f ∘ v
  have hg : AnalyticAt ℂ g (mobiusCoordinate x) := hf.comp_of_eq hv hvx
  have hgf : (g ∘ mobiusCoordinate) =ᶠ[𝓝 x] f := by
    filter_upwards [hleft] with z hz
    change v (mobiusCoordinate z) = z at hz
    change f (v (mobiusCoordinate z)) = f z
    rw [hz]
  have hP : zagierPullbackAnalyticODE (g ∘ mobiusCoordinate) =ᶠ[𝓝 x] 0 :=
    (eventuallyEq_zagierPullbackAnalyticODE hgf).trans he
  have hE : (zagierAnalyticODE g ∘ mobiusCoordinate) =ᶠ[𝓝 x] 0 := by
    filter_upwards [eventually_ne_nhds hx₁, hP,
      (analyticAt_mobiusCoordinate hx₁).continuousAt.tendsto.eventually hg.eventually_analyticAt]
      with z hz hPz hgz
    have h := zagierPullbackAnalyticODE_comp_mobiusCoordinate hz hgz
    rw [hPz, Pi.zero_apply] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero 3 (sub_ne_zero.mpr hz))
  have hv' : Tendsto v (𝓝 (mobiusCoordinate x)) (𝓝 x) := by
    simpa only [hvx] using hv.continuousAt.tendsto
  refine ⟨g, hg, ?_, hgf⟩
  filter_upwards [hE.comp_tendsto hv', hright] with y hy hvy
  change mobiusCoordinate (v y) = y at hvy
  change zagierAnalyticODE g (mobiusCoordinate (v y)) = 0 at hy
  simpa only [hvy] using hy

theorem exists_zagierAnalyticODE_of_secondOrder {f : ℂ → ℂ} {x : ℂ}
    (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) (hx₂ : x ≠ 2)
    (hf : AnalyticAt ℂ f x) (he : zagierSecondOrderODE f =ᶠ[𝓝 x] 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (mobiusCoordinate x) ∧
      zagierAnalyticODE g =ᶠ[𝓝 (mobiusCoordinate x)] 0 ∧
        (g ∘ mobiusCoordinate) =ᶠ[𝓝 x] f :=
  exists_zagierAnalyticODE_of_pullback hx₀ hx₁ hx₂ hf
    (eventually_zagierPullbackAnalyticODE_of_secondOrder hf he)

end DirichletL

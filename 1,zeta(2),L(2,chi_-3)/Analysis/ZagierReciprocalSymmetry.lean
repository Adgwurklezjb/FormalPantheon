import Analysis.ZagierEndpointSymmetry

/-!
Reciprocal symmetry of the scalar operator in CDT v2, Proposition `functionsH`.
The exact change of coordinate produces homogeneous solutions near infinity
and one, used to detect nonzero forcing in the `14functions` argument.
-/

namespace DirichletL

open Filter
open scoped Topology

/-- The reciprocal coordinate exchanging zero and infinity in the Zagier equation. -/
noncomputable def zagierReciprocalCoordinate (z : ℂ) : ℂ := 1 / (9 * z)

@[simp] theorem zagierReciprocalCoordinate_zero : zagierReciprocalCoordinate 0 = 0 := by
  simp [zagierReciprocalCoordinate]

@[simp] theorem zagierReciprocalCoordinate_one :
    zagierReciprocalCoordinate 1 = (9 : ℂ)⁻¹ := by
  norm_num [zagierReciprocalCoordinate]

theorem zagierReciprocalCoordinate_ne_zero {z : ℂ} (hz : z ≠ 0) :
    zagierReciprocalCoordinate z ≠ 0 :=
  one_div_ne_zero (mul_ne_zero (by norm_num) hz)

@[simp] theorem zagierReciprocalCoordinate_self (z : ℂ) :
    zagierReciprocalCoordinate (zagierReciprocalCoordinate z) = z := by
  by_cases hz : z = 0
  · simp [hz]
  · dsimp [zagierReciprocalCoordinate]
    field_simp [hz]

theorem analyticAt_zagierReciprocalCoordinate {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ zagierReciprocalCoordinate z :=
  analyticAt_const.div (analyticAt_const.mul analyticAt_id) (mul_ne_zero (by norm_num) hz)

theorem hasDerivAt_zagierReciprocalCoordinate {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt zagierReciprocalCoordinate (-1 / (9 * z ^ 2)) z := by
  have h := (hasDerivAt_const z (1 : ℂ)).div ((hasDerivAt_id z).const_mul 9)
    (mul_ne_zero (by norm_num) hz)
  convert h using 1
  dsimp
  field_simp [hz]
  ring

/-- The weight factor for the reciprocal symmetry of the original scalar equation. -/
noncomputable def zagierReciprocalTransform (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f (zagierReciprocalCoordinate z) / z

theorem analyticAt_zagierReciprocalTransform {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hf : AnalyticAt ℂ f (zagierReciprocalCoordinate z)) :
    AnalyticAt ℂ (zagierReciprocalTransform f) z :=
  (hf.comp (analyticAt_zagierReciprocalCoordinate hz)).div analyticAt_id hz

theorem hasDerivAt_zagierReciprocalTransform {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hf : DifferentiableAt ℂ f (zagierReciprocalCoordinate z)) :
    HasDerivAt (zagierReciprocalTransform f)
      (-f (zagierReciprocalCoordinate z) / z ^ 2 -
        (1 / 9) * deriv f (zagierReciprocalCoordinate z) / z ^ 3) z := by
  have h := (hf.hasDerivAt.comp z (hasDerivAt_zagierReciprocalCoordinate hz)).div
    (hasDerivAt_id z) hz
  convert h using 1
  dsimp
  field_simp [hz]
  ring

theorem hasDerivAt_deriv_zagierReciprocalTransform {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hf : AnalyticAt ℂ f (zagierReciprocalCoordinate z)) :
    HasDerivAt (deriv (zagierReciprocalTransform f))
      (2 * f (zagierReciprocalCoordinate z) / z ^ 3 +
        (4 / 9) * deriv f (zagierReciprocalCoordinate z) / z ^ 4 +
        (1 / 81) * deriv (deriv f) (zagierReciprocalCoordinate z) / z ^ 5) z := by
  have ht := hasDerivAt_zagierReciprocalCoordinate hz
  have h0 := hf.differentiableAt.hasDerivAt.comp z ht
  have h1 := hf.deriv.differentiableAt.hasDerivAt.comp z ht
  have h := (h0.neg.div ((hasDerivAt_id z).pow 2) (pow_ne_zero 2 hz)).sub
    ((h1.const_mul (1 / 9)).div ((hasDerivAt_id z).pow 3) (pow_ne_zero 3 hz))
  have he : deriv (zagierReciprocalTransform f) =ᶠ[𝓝 z] fun w =>
      -f (zagierReciprocalCoordinate w) / w ^ 2 -
        (1 / 9) * deriv f (zagierReciprocalCoordinate w) / w ^ 3 := by
    filter_upwards [eventually_ne_nhds hz,
      (analyticAt_zagierReciprocalCoordinate hz).continuousAt.tendsto.eventually
        hf.eventually_analyticAt] with w hw hwf
    exact (hasDerivAt_zagierReciprocalTransform hw hwf.differentiableAt).deriv
  convert h.congr_of_eventuallyEq he using 1
  dsimp
  field_simp (discharger := simp [hz]) [hz]
  ring

theorem zagierSecondOrderODE_reciprocalTransform {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hf : AnalyticAt ℂ f (zagierReciprocalCoordinate z)) :
    zagierSecondOrderODE (zagierReciprocalTransform f) z =
      zagierSecondOrderODE f (zagierReciprocalCoordinate z) / z := by
  rw [zagierSecondOrderODE, (hasDerivAt_deriv_zagierReciprocalTransform hz hf).deriv,
    (hasDerivAt_zagierReciprocalTransform hz hf.differentiableAt).deriv]
  dsimp [zagierSecondOrderODE, zagierReciprocalTransform]
  generalize f (zagierReciprocalCoordinate z) = f₀
  generalize deriv f (zagierReciprocalCoordinate z) = f₁
  generalize deriv (deriv f) (zagierReciprocalCoordinate z) = f₂
  dsimp [zagierReciprocalCoordinate]
  field_simp (discharger := simp [hz]) [hz]
  ring

theorem eventually_zagierSecondOrderODE_reciprocalTransform {f : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 0) (hf : AnalyticAt ℂ f (zagierReciprocalCoordinate z))
    (he : zagierSecondOrderODE f =ᶠ[𝓝 (zagierReciprocalCoordinate z)] 0) :
    zagierSecondOrderODE (zagierReciprocalTransform f) =ᶠ[𝓝 z] 0 := by
  have ht := (analyticAt_zagierReciprocalCoordinate hz).continuousAt.tendsto
  filter_upwards [eventually_ne_nhds hz, ht.eventually hf.eventually_analyticAt,
    he.comp_tendsto ht] with w hw hwf hwe
  dsimp only [Function.comp_apply, Pi.zero_apply] at hwe
  rw [zagierSecondOrderODE_reciprocalTransform hw hwf, hwe, Pi.zero_apply, zero_div]

end DirichletL

import Mathlib

/-!
Inner dilation in CDT v2 TeX 4150-4153 and the clearing explanation at 5235.
-/

namespace DirichletL

theorem meromorphicAt_comp_const_mul {f : ℂ → ℂ} {a x : ℂ} (ha : a ≠ 0)
    (hf : MeromorphicAt f (a * x)) : MeromorphicAt (fun z => f (a * z)) x := by
  obtain ⟨n, hn⟩ := hf
  have hcomp : AnalyticAt ℂ (fun z => (a * z - a * x) ^ n * f (a * z)) x := by
    simpa only [smul_eq_mul] using
      hn.comp' (analyticAt_const.mul analyticAt_id :
        AnalyticAt ℂ (fun z : ℂ => a * z) x)
  have hscaled : AnalyticAt ℂ
      (fun z => (a ^ n)⁻¹ * ((a * z - a * x) ^ n * f (a * z))) x :=
    analyticAt_const.mul hcomp
  refine ⟨n, ?_⟩
  convert hscaled using 1
  funext z
  rw [smul_eq_mul, ← mul_sub, mul_pow]
  field_simp [pow_ne_zero n ha]

end DirichletL

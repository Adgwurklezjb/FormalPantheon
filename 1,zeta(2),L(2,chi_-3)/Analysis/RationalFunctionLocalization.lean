import Analysis.RationalFunctionCalculus

/-!
The coefficient localization in CDT v2, `14functions`, between
`simpleagain` and `explicitode` (supplied TeX lines 8099-8140).
-/

namespace DirichletL

open Polynomial

/-- The canonical polynomial localization inside the rational function field. -/
noncomputable def ratFuncAway (p : ℂ[X]) (hp : p ≠ 0) : Subalgebra ℂ[X] (RatFunc ℂ) :=
  Localization.subalgebra.ofField (RatFunc ℂ) (Submonoid.powers p)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hp)

theorem mem_ratFuncAway_iff {p : ℂ[X]} {hp : p ≠ 0} {B : RatFunc ℂ} :
    B ∈ ratFuncAway p hp ↔ ∃ n : ℕ, B.denom ∣ p ^ n := by
  change (∃ (a s : ℂ[X]) (_ : s ∈ Submonoid.powers p),
    B = algebraMap ℂ[X] (RatFunc ℂ) a * (algebraMap ℂ[X] (RatFunc ℂ) s)⁻¹) ↔ _
  constructor
  · rintro ⟨a, s, hs, hB⟩
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff s p).mp hs
    exact ⟨n, (RatFunc.denom_dvd (pow_ne_zero n hp)).mpr
      ⟨a, by simpa only [div_eq_mul_inv] using hB⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨a, ha⟩ := (RatFunc.denom_dvd (pow_ne_zero n hp)).mp hn
    exact ⟨a, p ^ n, ⟨n, rfl⟩, by simpa only [div_eq_mul_inv] using ha⟩

theorem ratFuncDerivative_mem_ratFuncAway {p : ℂ[X]} {hp : p ≠ 0} {B : RatFunc ℂ}
    (hB : B ∈ ratFuncAway p hp) : ratFuncDerivative B ∈ ratFuncAway p hp := by
  obtain ⟨n, hn⟩ := mem_ratFuncAway_iff.mp hB
  apply mem_ratFuncAway_iff.mpr
  refine ⟨n * 2, ?_⟩
  rw [pow_mul]
  exact (denom_ratFuncDerivative_dvd B).trans (pow_dvd_pow_of_dvd hn 2)

theorem polynomial_div_mem_ratFuncAway {p : ℂ[X]} {hp : p ≠ 0} (a q : ℂ[X])
    (hq : ∃ n : ℕ, q ∣ p ^ n) :
    algebraMap ℂ[X] (RatFunc ℂ) a / algebraMap ℂ[X] (RatFunc ℂ) q ∈ ratFuncAway p hp := by
  obtain ⟨n, hn⟩ := hq
  exact mem_ratFuncAway_iff.mpr ⟨n, (RatFunc.denom_div_dvd a q).trans hn⟩

end DirichletL

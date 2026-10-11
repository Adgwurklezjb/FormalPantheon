import Arithmetic.BalancedCardinalityAsymptotic

/-!
Cutoff and dimension limits in the order specified by CDT v2 TeX 4002-4004.
-/

namespace DirichletL

open Filter
open scoped Topology

theorem partition_holonomy_le_of_eventually {s : ℕ} {W κ η J ξ ε B ζ C c K δ : ℝ}
    (hbound : ∀ᶠ h : ℕ in atTop, ∀ᶠ D : ℕ in atTop,
      (14 + δ) * W ≤ 14 * (κ + η) + J + 4 * ξ + 2 * ε * B + 2 * ζ +
        (2 * (Real.log 14 + Real.log D) + 2 * C + 4 * Real.log (14 * h : ℕ)) / D +
        (4 * B / c) * Real.log (14 * h : ℕ) / (14 * h : ℕ) +
        (14 + δ) * (2 * ε * K + 3 * (s : ℝ) * K / (14 * h : ℕ))) :
    (14 + δ) * W ≤ 14 * (κ + η) + J + 4 * ξ + 2 * ε * B + 2 * ζ +
      (14 + δ) * (2 * ε * K) := by
  let P : ℝ := 14 * (κ + η) + J + 4 * ξ + 2 * ε * B + 2 * ζ
  have hlogD : Tendsto (fun D : ℕ => Real.log (D : ℝ) / D) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_mul, Nat.add_zero] using tendsto_log_nat_affine_div 1 0 (by decide)
  have hdimBound : ∀ᶠ h : ℕ in atTop,
      (14 + δ) * W ≤ P + (4 * B / c) * Real.log (14 * h : ℕ) / (14 * h : ℕ) +
        (14 + δ) * (2 * ε * K + 3 * (s : ℝ) * K / (14 * h : ℕ)) := by
    filter_upwards [hbound] with h hh
    let d : ℕ := 14 * h
    have hknown : Tendsto (fun D : ℕ => 2 * (Real.log (D : ℝ) / D) +
        (2 * Real.log 14 + 2 * C + 4 * Real.log d) / D) atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero, add_zero] using (hlogD.const_mul 2).add
        (tendsto_const_div_atTop_nhds_zero_nat (2 * Real.log 14 + 2 * C + 4 * Real.log d))
    have htermD : Tendsto (fun D : ℕ =>
        (2 * (Real.log 14 + Real.log D) + 2 * C + 4 * Real.log d) / D)
        atTop (𝓝 (0 : ℝ)) := by
      convert hknown using 1
      ext D
      ring
    have hlim : Tendsto (fun D : ℕ => P +
        (2 * (Real.log 14 + Real.log D) + 2 * C + 4 * Real.log d) / D +
        (4 * B / c) * Real.log d / d + (14 + δ) * (2 * ε * K + 3 * (s : ℝ) * K / d))
        atTop (𝓝 (P + (4 * B / c) * Real.log d / d +
          (14 + δ) * (2 * ε * K + 3 * (s : ℝ) * K / d))) := by
      simpa only [add_zero] using ((htermD.const_add P).add_const
        ((4 * B / c) * Real.log d / d)).add_const
          ((14 + δ) * (2 * ε * K + 3 * (s : ℝ) * K / d))
    exact ge_of_tendsto hlim hh
  have hlogdim : Tendsto (fun h : ℕ =>
      Real.log (14 * h : ℕ) / (14 * h : ℕ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.add_zero] using tendsto_log_nat_affine_div 14 0 (by decide)
  have hdim : Tendsto (fun h : ℕ => ((14 * h : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 14)
        (tendsto_natCast_atTop_atTop : Tendsto (fun h : ℕ => (h : ℝ)) atTop atTop)
  have hconstdim : Tendsto (fun h : ℕ => 3 * (s : ℝ) * K / (14 * h : ℕ))
      atTop (𝓝 (0 : ℝ)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => 3 * (s : ℝ) * K)
      atTop (𝓝 (3 * (s : ℝ) * K))).div_atTop hdim
  have hlim : Tendsto (fun h : ℕ => P +
      (4 * B / c) * (Real.log (14 * h : ℕ) / (14 * h : ℕ)) +
      (14 + δ) * (2 * ε * K + 3 * (s : ℝ) * K / (14 * h : ℕ)))
      atTop (𝓝 (P + (14 + δ) * (2 * ε * K))) := by
    simpa only [mul_zero, add_zero] using
      ((hlogdim.const_mul (4 * B / c)).const_add P).add
        ((hconstdim.const_add (2 * ε * K)).const_mul (14 + δ))
  apply ge_of_tendsto hlim
  filter_upwards [hdimBound] with h hh
  convert hh using 1
  ring

end DirichletL

import Mathlib

/-!
Exact scalar steps for CDT v2 TeX 3503-3541, 3998-4028, and 4188-4229.
-/

namespace DirichletL

theorem partition_holonomy_normalized_bound {d D s M : ℕ} (hd : 0 < d) (hD : 0 < D)
    {W κ η J ξ ε B ζ C c K Qlog δ : ℝ} (hδ : 0 < 14 + δ) (hc : c ≠ 0)
    (hQ : Qlog ≤ (d : ℝ) * (Real.log 14 + Real.log D))
    (hM : (M : ℝ) ≤ (2 * B / c) * D / d + 2)
    (hbound : W ≤
      2 * (7 * (d : ℝ) * D * (κ + η) + Qlog + ζ * d * D + d * C +
        (D : ℝ) * d * (J / 2 + 2 * ξ + ε * B) + M * d * Real.log d) /
          ((14 + δ) * D * d) + 2 * ε * K + 3 * (s : ℝ) * K / d) :
    (14 + δ) * W ≤ 14 * (κ + η) + J + 4 * ξ + 2 * ε * B + 2 * ζ +
      (2 * (Real.log 14 + Real.log D) + 2 * C + 4 * Real.log d) / D +
      (4 * B / c) * Real.log d / d +
      (14 + δ) * (2 * ε * K + 3 * (s : ℝ) * K / d) := by
  have hQ' : 2 * Qlog / ((D : ℝ) * d) ≤
      2 * (Real.log 14 + Real.log D) / D := by
    calc
      _ = (2 / ((D : ℝ) * d)) * Qlog := by ring
      _ ≤ (2 / ((D : ℝ) * d)) * ((d : ℝ) * (Real.log 14 + Real.log D)) :=
        mul_le_mul_of_nonneg_left hQ (by positivity)
      _ = _ := by
        field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast hd.ne',
          show (D : ℝ) ≠ 0 by exact_mod_cast hD.ne']
  have hM' : 2 * (M : ℝ) * Real.log d / D ≤
      (4 * B / c) * Real.log d / d + 4 * Real.log d / D := by
    calc
      _ = (2 * Real.log (d : ℝ) / D) * M := by ring
      _ ≤ (2 * Real.log (d : ℝ) / D) * ((2 * B / c) * D / d + 2) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = _ := by
        field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast hd.ne',
          show (D : ℝ) ≠ 0 by exact_mod_cast hD.ne', hc]
        ring
  calc
    _ ≤ (14 + δ) *
        (2 * (7 * (d : ℝ) * D * (κ + η) + Qlog + ζ * d * D + d * C +
          (D : ℝ) * d * (J / 2 + 2 * ξ + ε * B) + M * d * Real.log d) /
            ((14 + δ) * D * d) + 2 * ε * K + 3 * (s : ℝ) * K / d) :=
      mul_le_mul_of_nonneg_left hbound hδ.le
    _ = 14 * (κ + η) + J + 4 * ξ + 2 * ε * B + 2 * ζ +
        2 * Qlog / ((D : ℝ) * d) + 2 * C / D + 2 * M * Real.log d / D +
        (14 + δ) * (2 * ε * K + 3 * (s : ℝ) * K / d) := by
      field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast hd.ne',
        show (D : ℝ) ≠ 0 by exact_mod_cast hD.ne', hδ.ne']
      ring
    _ ≤ _ := by
      simp only [div_eq_mul_inv] at hQ' hM' ⊢
      linarith only [hQ', hM']

theorem partition_holonomy_remove_delta {W T B K ε' ε δ : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hε' : 0 ≤ ε') (hε'ε : ε' ≤ ε)
    (hδ : 0 ≤ δ) (hδε' : δ ≤ ε') (hδ1 : δ ≤ 1)
    (hbound : (14 + δ) * W ≤ T + 2 * ε' * B + (14 + δ) * (2 * ε' * K)) :
    14 * W ≤ T + ε * (2 * B + 30 * K + |W|) := by
  have hB' : 2 * ε' * B ≤ 2 * ε * B :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hε'ε (by norm_num)) hB
  have hεK : 2 * ε' * K ≤ 2 * ε * K :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hε'ε (by norm_num)) hK
  have hK' : (14 + δ) * (2 * ε' * K) ≤ 30 * ε * K := by
    calc
      _ ≤ 15 * (2 * ε' * K) :=
        mul_le_mul_of_nonneg_right (by linarith only [hδ1]) (by positivity)
      _ ≤ 15 * (2 * ε * K) := mul_le_mul_of_nonneg_left hεK (by norm_num)
      _ = _ := by ring
  have hneg : -δ * W ≤ ε * |W| := by
    calc
      _ = δ * (-W) := by ring
      _ ≤ δ * |W| := mul_le_mul_of_nonneg_left (neg_le_abs W) hδ
      _ ≤ ε * |W| := mul_le_mul_of_nonneg_right (hδε'.trans hε'ε) (abs_nonneg W)
  nlinarith only [hbound, hB', hK', hneg]

theorem partition_holonomy_le_of_errors {W κ J B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbound : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∀ ξ : ℝ, 0 < ξ →
      ∀ ζ : ℝ, 0 < ζ → 14 * W ≤ 14 * κ + J + 14 * η + 4 * ξ + 2 * ζ +
        ε * (2 * B + 30 * K + |W|)) :
    14 * W ≤ 14 * κ + J := by
  by_contra! hlt
  let g : ℝ := 14 * W - (14 * κ + J)
  have hg : 0 < g := sub_pos.mpr hlt
  let T : ℝ := 20 + 2 * B + 30 * K + |W|
  let τ : ℝ := g / (2 * T)
  have hτ : 0 < τ := div_pos hg (by positivity)
  have hsmall := hbound τ hτ τ hτ τ hτ τ hτ
  have heq : τ * T = g / 2 := by
    dsimp only [τ]
    field_simp [show T ≠ 0 by dsimp only [T]; positivity]
  dsimp only [g, T] at heq
  nlinarith only [hsmall, heq, hlt]

end DirichletL

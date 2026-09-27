import Analysis.LcmCutoffTwoSums
import Analysis.UniformSequenceLimits
import Arithmetic.LcmAsymptotic
import Arithmetic.LcmIntervalQuotientProducts

/-!
An exact common clearing integer and its normalized growth for the
fourteen-function family in CDT v2, supplied TeX 4440-4518.
The total exponent is six, the maximum exponent one, and the cutoff two.
Coordinate and exponent hypotheses remain explicit until the auxiliary
coefficient construction supplies them.
-/

namespace DirichletL

open Filter

/-- The prefix and horizontal clearing integer at cutoff two. -/
def cdt14HorizontalDenominator (d D : ℕ) (n : ℕ → ℕ) : ℕ :=
  lcmPrefix (2 * D) ^ (3 * d / 7) *
    ∏ j ∈ Finset.range d, lcmIntervalQuotient (n j) D (2 * D)

theorem cdt14HorizontalDenominator_pos (d D : ℕ) (n : ℕ → ℕ) :
    0 < cdt14HorizontalDenominator d D n :=
  Nat.mul_pos (pow_pos (lcmPrefix_pos (2 * D)) _) (Finset.prod_pos
    (fun j _ => lcmIntervalQuotient_pos (n j) D (2 * D)))

theorem isInteger_cdt14HorizontalDenominator_mul_prod (d D : ℕ)
    (n r e : ℕ → ℕ) (q : ℕ → ℚ)
    (hlo : ∀ j < d, n j - D ≤ r j) (hhi : ∀ j < d, r j ≤ n j)
    (he : ∀ j < d, e j ≤ 1) (hsum : (∑ j ∈ Finset.range d, e j) ≤ 3 * d / 7)
    (hzero : ∀ j < d, r j = 0 → IsLocalization.IsInteger ℤ (q j))
    (hcoeff : ∀ j < d, IsLocalization.IsInteger ℤ ((r j : ℚ) ^ e j * q j)) :
    IsLocalization.IsInteger ℤ
      ((cdt14HorizontalDenominator d D n : ℚ) * ∏ j ∈ Finset.range d, q j) := by
  have hclear := isInteger_prefix_mul_quotient_prod (Finset.range d) n r e q D (2 * D) 1
    (fun j hj => hlo j (Finset.mem_range.mp hj))
    (fun j hj => hhi j (Finset.mem_range.mp hj))
    (fun j hj => he j (Finset.mem_range.mp hj))
    (fun j hj => hzero j (Finset.mem_range.mp hj))
    (fun j hj => hcoeff j (Finset.mem_range.mp hj))
  apply isInteger_nat_mul_of_dvd hclear
  simp only [pow_one, cdt14HorizontalDenominator]
  exact mul_dvd_mul_right (pow_dvd_pow _ hsum) _

theorem log_cdt14HorizontalDenominator (d D : ℕ) (n : ℕ → ℕ) :
    Real.log (cdt14HorizontalDenominator d D n : ℝ) =
      ((3 * d / 7 : ℕ) : ℝ) * Real.log (lcmPrefix (2 * D) : ℝ) +
        ∑ j ∈ Finset.range d, Real.log (lcmIntervalQuotient (n j) D (2 * D) : ℝ) := by
  have hP : ((lcmPrefix (2 * D) ^ (3 * d / 7) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (pow_pos (lcmPrefix_pos (2 * D)) (3 * d / 7)).ne'
  have hQ : ((∏ j ∈ Finset.range d, lcmIntervalQuotient (n j) D (2 * D) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.prod_pos (fun j _ => lcmIntervalQuotient_pos (n j) D (2 * D))).ne'
  rw [cdt14HorizontalDenominator, Nat.cast_mul, Real.log_mul hP hQ,
    Nat.cast_pow, Real.log_pow, Nat.cast_prod, Real.log_prod _ _ (fun j _ => by
      exact_mod_cast (lcmIntervalQuotient_pos (n j) D (2 * D)).ne')]

theorem eventually_log_cdt14HorizontalDenominator_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ D : ℕ in atTop, ∀ d : ℕ, 0 < d → ∀ δ : ℝ, 0 ≤ δ → δ ≤ 2 →
      ∀ n : ℕ → ℕ,
        (∀ j < d, (n j : ℝ) ≤ (D : ℝ) * (δ + 14 * ((j : ℝ) + 1) / (d : ℝ))) →
        Real.log (cdt14HorizontalDenominator d D n : ℝ) ≤
          7 * (d : ℝ) * (D : ℝ) * ((27 / 80 : ℝ) + δ * (harmonic 7 : ℝ) / 98 +
            (harmonic 7 : ℝ) / (7 * (d : ℝ)) + (10 / 49 : ℝ) * η) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_abs_initialSegment_sub_le tendsto_log_lcmPrefix_div (half_pos hη))
  filter_upwards [eventually_ge_atTop N, eventually_log_lcmIntervalQuotient_prod_le hη]
    with D hDN hQ d hd δ hδ0 hδ2 n hn
  have hprefix : Real.log (lcmPrefix (2 * D) : ℝ) ≤ (2 + η) * (D : ℝ) := by
    have he := (abs_le.mp (hN (2 * D) (by omega) (2 * D) le_rfl)).2
    push_cast at he
    linarith only [he]
  have hexponent : ((3 * d / 7 : ℕ) : ℝ) ≤ (3 / 7 : ℝ) * (d : ℝ) := by
    calc
      _ ≤ ((3 * d : ℕ) : ℝ) / ((7 : ℕ) : ℝ) := Nat.cast_div_le
      _ = _ := by push_cast; ring
  have hbase : 0 ≤ (2 + η) * (D : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg D)
  have hpe := mul_le_mul_of_nonneg_left hprefix (Nat.cast_nonneg (3 * d / 7) :
    (0 : ℝ) ≤ ((3 * d / 7 : ℕ) : ℝ))
  have hpe' := mul_le_mul_of_nonneg_right hexponent hbase
  have hprod := hQ d hd δ hδ0 hδ2 n hn
  rw [Nat.cast_prod, Real.log_prod _ _ (fun j _ => by
    exact_mod_cast (lcmIntervalQuotient_pos (n j) D (2 * D)).ne')] at hprod
  rw [log_cdt14HorizontalDenominator]
  calc
    _ ≤ ((3 / 7 : ℝ) * (d : ℝ)) * ((2 + η) * (D : ℝ)) +
        (d : ℝ) * (D : ℝ) * ((843 / 560 : ℝ) + δ * (harmonic 7 : ℝ) / 14 +
          (harmonic 7 : ℝ) / (d : ℝ) + η) := add_le_add (hpe.trans hpe') hprod
    _ = _ := by field_simp; ring

theorem exists_delta_eventually_log_cdt14HorizontalDenominator_le {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ᶠ d : ℕ in atTop, ∀ᶠ D : ℕ in atTop,
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ₀ → ∀ n : ℕ → ℕ,
        (∀ j < d, (n j : ℝ) ≤ (D : ℝ) * (δ + 14 * ((j : ℝ) + 1) / (d : ℝ))) →
        Real.log (cdt14HorizontalDenominator d D n : ℝ) ≤
          7 * (d : ℝ) * (D : ℝ) * ((27 / 80 : ℝ) + ε) := by
  refine ⟨min 1 ε, lt_min (by norm_num) hε, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ), eventually_ge_atTop ⌈1 / ε⌉₊] with d hd hdε
  filter_upwards [eventually_log_cdt14HorizontalDenominator_le hε] with D hD δ hδ hδmax n hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hδ1 : δ ≤ 1 := hδmax.trans (min_le_left 1 ε)
  have hδε : δ ≤ ε := hδmax.trans (min_le_right 1 ε)
  have hlarge : 1 / ε ≤ (d : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hdε)
  have hinv : 1 / (d : ℝ) ≤ ε := by
    apply (div_le_iff₀ hdR).mpr
    have h := (div_le_iff₀ hε).mp hlarge
    nlinarith only [h]
  have hH : (harmonic 7 : ℝ) ≤ 3 := by norm_num [harmonic, Finset.sum_range_succ]
  have hfirst : δ * (harmonic 7 : ℝ) / 98 ≤ 3 * ε / 98 := by
    have h := mul_le_mul_of_nonneg_left hH hδ
    linarith only [h, hδε]
  have hsecond : (harmonic 7 : ℝ) / (7 * (d : ℝ)) ≤ 3 * ε / 7 := by
    have h := div_le_div_of_nonneg_right hH hdR.le
    have hi : (3 : ℝ) / (d : ℝ) ≤ 3 * ε := by
      simpa only [mul_one_div] using
        mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 3)
    have he : (harmonic 7 : ℝ) / (7 * (d : ℝ)) = ((harmonic 7 : ℝ) / (d : ℝ)) / 7 := by
      ring
    rw [he]
    linarith only [h, hi]
  have herr : (27 / 80 : ℝ) + δ * (harmonic 7 : ℝ) / 98 +
      (harmonic 7 : ℝ) / (7 * (d : ℝ)) + (10 / 49 : ℝ) * ε ≤ (27 / 80 : ℝ) + ε := by
    linarith only [hfirst, hsecond, hε]
  exact (hD d hd δ hδ (by linarith only [hδ1]) n hn).trans
    (mul_le_mul_of_nonneg_left herr (by positivity))

end DirichletL

import Analysis.PowerSeriesCompositionAnalytic
import Arithmetic.PowerSeriesInverse

/-!
Convergence of the existing rational reversion via Mathlib's analytic formal
inverse. This is the coefficient-compatibility input for CDT v2, Section 11.1,
-/

namespace DirichletL

theorem pos_radius_complexSeries_reversion {f : PowerSeries ℚ}
    (hf : 0 < (complexSeries f).radius)
    (hf0 : PowerSeries.constantCoeff (R := ℚ) f = 0) (hf1 : PowerSeries.coeff (R := ℚ) 1 f = 1) :
    0 < (complexSeries (reversion f)).radius := by
  let p := complexSeries f
  let i := ContinuousLinearEquiv.refl ℂ ℂ
  have hlin : p 1 = (continuousMultilinearCurryFin1 ℂ ℂ ℂ).symm i := by
    ext v
    simp [p, complexSeries, FormalMultilinearSeries.ofScalars, hf1, i]
  have hcomp := p.leftInv_comp i 0 hlin
  have hid (n : ℕ) : (FormalMultilinearSeries.id ℂ ℂ 0).coeff n =
      if n = 1 then 1 else 0 := by
    rcases n with _ | (_ | n)
    · simp [FormalMultilinearSeries.coeff, FormalMultilinearSeries.id]
    · simp [FormalMultilinearSeries.coeff, FormalMultilinearSeries.id]
    · simp [FormalMultilinearSeries.coeff, FormalMultilinearSeries.id]
  have hcoeff (n : ℕ) : (p.leftInv i 0).coeff n = ((reversionCoeff f n : ℚ) : ℂ) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have h := congrArg (fun s : FormalMultilinearSeries ℂ ℂ ℂ => s.coeff n) hcomp
      change ((p.leftInv i 0).comp (complexSeries f)).coeff n =
        (FormalMultilinearSeries.id ℂ ℂ 0).coeff n at h
      rw [coeff_comp_complexSeries hf hf0, hid, Finset.sum_range_succ,
        coeff_pow_self_of_constantCoeff_zero f hf0, hf1, one_pow, Rat.cast_one, mul_one] at h
      rw [reversionCoeff_eq]
      simp only [Rat.cast_sub, Rat.cast_sum, Rat.cast_mul, apply_ite,
        Rat.cast_one, Rat.cast_zero]
      have hs : (∑ k ∈ Finset.range n,
          (p.leftInv i 0).coeff k * (PowerSeries.coeff (R := ℚ) n (f ^ k) : ℂ)) =
          ∑ k ∈ Finset.range n,
            ((reversionCoeff f k : ℚ) : ℂ) * (PowerSeries.coeff (R := ℚ) n (f ^ k) : ℂ) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ih k (Finset.mem_range.mp hk)]
      rw [hs] at h
      linear_combination h
  have he : complexSeries (reversion f) = p.leftInv i 0 := by
    ext n v
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      FormalMultilinearSeries.apply_eq_prod_smul_coeff, hcoeff,
      coeff_complexSeries, coeff_reversion]
  rw [he]
  exact FormalMultilinearSeries.radius_leftInv_pos_of_radius_pos hf hlin

end DirichletL

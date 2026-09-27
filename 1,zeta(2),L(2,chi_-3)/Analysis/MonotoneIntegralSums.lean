import Mathlib

/-!
The finite right-sum error used in CDT v2, supplied TeX 4480-4518.
The native monotone lower-sum comparison and affine substitution give
an explicit endpoint error, without any differentiability assumption.
-/

namespace DirichletL

theorem sum_right_grid_le_integral {f : ℝ → ℝ} (hf : Monotone f)
    (a : ℝ) {L : ℝ} (hL : 0 < L) {d : ℕ} (hd : 0 < d) :
    (∑ j ∈ Finset.range d, f (a + L * ((j : ℝ) + 1) / (d : ℝ))) / (d : ℝ) ≤
      (∫ t in a..a + L, f t) / L + (f (a + L) - f a) / (d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let g : ℝ → ℝ := fun x => f (a + (L / (d : ℝ)) * x)
  have hg : Monotone g := fun _ _ h =>
    hf (add_le_add_left (mul_le_mul_of_nonneg_left h (div_pos hL hdR).le) a)
  have hleft : (∑ j ∈ Finset.range d, g (j : ℝ)) ≤ ∫ x in (0 : ℝ)..d, g x := by
    simpa only [zero_add] using
      (hg.monotoneOn (Set.Icc 0 (0 + (d : ℝ)))).sum_le_integral
  have hdiff : (∑ j ∈ Finset.range d, g ((j : ℝ) + 1)) -
      (∑ j ∈ Finset.range d, g (j : ℝ)) = g (d : ℝ) - g 0 := by
    simpa only [Finset.sum_sub_distrib, Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
      Finset.sum_range_sub (fun j : ℕ => g (j : ℝ)) d
  have hends : g (d : ℝ) = f (a + L) := by simp [g, hdR.ne']
  have hzero : g 0 = f a := by simp [g]
  have hint : (L / (d : ℝ)) * (∫ x in (0 : ℝ)..d, g x) = ∫ t in a..a + L, f t := by
    simpa only [g, mul_zero, add_zero, div_mul_cancel₀ L hdR.ne'] using
      intervalIntegral.mul_integral_comp_add_mul (f := f) (a := 0) (b := (d : ℝ))
        (L / (d : ℝ)) a
  have hscaled : (∫ x in (0 : ℝ)..d, g x) / (d : ℝ) =
      (∫ t in a..a + L, f t) / L := by
    rw [← hint]
    field_simp
  have hright : (∑ j ∈ Finset.range d, g ((j : ℝ) + 1)) ≤
      (∫ x in (0 : ℝ)..d, g x) + (f (a + L) - f a) := by
    rw [hends, hzero] at hdiff
    linarith only [hleft, hdiff]
  have hbound := div_le_div_of_nonneg_right hright hdR.le
  rw [add_div, hscaled] at hbound
  simpa only [g, div_mul_eq_mul_div] using hbound

end DirichletL

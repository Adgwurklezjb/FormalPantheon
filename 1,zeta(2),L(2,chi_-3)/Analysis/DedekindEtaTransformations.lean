import Analysis.DedekindEta
import Analysis.ThetaTransformations

/-!
The S and T transformations of Dedekind eta, DLMF 23.18.5-7 and 27.14.12.
Theta inversion first proves the cubic S identity. Continuity and the
fixed point I determine its root of unity with the principal square root.
-/

namespace DirichletL

open Complex Function.Periodic
open scoped Real

private theorem eta_neg_inv_im_pos {τ : ℂ} (hτ : 0 < τ.im) : 0 < (-1 / τ).im := by
  simpa only [UpperHalfPlane.coe_mk, inv_neg, neg_div, one_div] using
    (UpperHalfPlane.im_inv_neg_coe_pos ⟨τ, hτ⟩)

theorem dedekindEta_neg_inv_pow_three {τ : ℂ} (hτ : 0 < τ.im) :
    dedekindEta (-1 / τ) ^ 3 = ((-I * τ) ^ (1 / 2 : ℂ)) ^ 3 * dedekindEta τ ^ 3 := by
  have h0 : τ ≠ 0 := fun h => (ne_of_gt hτ) (congrArg Complex.im h)
  have hh : 0 < (τ / 2).im := by simpa using half_pos hτ
  have hi : 0 < ((-1 / τ) / 2).im := by simpa using half_pos (eta_neg_inv_im_pos hτ)
  have htwo : 2 * (τ / 2) = τ := by ring
  have htwoi : 2 * ((-1 / τ) / 2) = -1 / τ := by ring
  have hcoord : -1 / (4 * (τ / 2)) = (-1 / τ) / 2 := by field_simp; ring
  have h3 := sum_complexSeries_thetaThreeSeries_inversion hh
  have h4 := sum_complexSeries_thetaFourSeries_inversion hh
  have h2 := sum_complexSeries_thetaTwoNormalizedSeries_inversion hh
  rw [htwo, hcoord] at h3 h4 h2
  have hc := dedekindEta_two_mul_pow_three hh
  have hci := dedekindEta_two_mul_pow_three hi
  rw [htwo] at hc
  rw [htwoi] at hci
  have he : exp (-π * I / (8 * (τ / 2))) = exp (π * I * ((-1 / τ) / 2) / 2) := by
    congr 1
    field_simp
    ring
  rw [he] at h4
  have hn : exp (-π * I * (τ / 2) / 2) = (exp (π * I * (τ / 2) / 2))⁻¹ := by
    rw [← exp_neg]
    congr 1
    ring
  have hs : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) h0))
  simp only [neg_mul] at hs
  rw [hci, hc, h3, h4, h2, hn]
  field_simp [hs]

private theorem continuousOn_eta_inversion_ratio :
    ContinuousOn (fun τ : ℂ => dedekindEta (-1 / τ) /
      ((-I * τ) ^ (1 / 2 : ℂ) * dedekindEta τ)) {τ : ℂ | 0 < τ.im} := by
  have h0 : ∀ τ : ℂ, 0 < τ.im → τ ≠ 0 :=
    fun τ hτ h => (ne_of_gt hτ) (congrArg Complex.im h)
  have hi : ContinuousOn (fun τ : ℂ => -1 / τ) {τ : ℂ | 0 < τ.im} :=
    continuousOn_const.div continuousOn_id h0
  have hn := differentiableOn_dedekindEta.continuousOn.comp hi
    (fun _ hτ => eta_neg_inv_im_pos hτ)
  apply hn.div
  · apply ContinuousOn.mul _ differentiableOn_dedekindEta.continuousOn
    apply (continuousOn_const.mul continuousOn_id).cpow_const
    intro τ hτ
    apply mem_slitPlane_iff.mpr
    left
    simpa using hτ
  · intro τ hτ
    exact mul_ne_zero
      (cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (h0 τ hτ))))
      (dedekindEta_ne_zero hτ)

private theorem eta_inversion_ratio_eq_one {τ : ℂ} (hτ : 0 < τ.im) :
    dedekindEta (-1 / τ) / ((-I * τ) ^ (1 / 2 : ℂ) * dedekindEta τ) = 1 := by
  let R : ℂ → ℂ := fun z => dedekindEta (-1 / z) /
    ((-I * z) ^ (1 / 2 : ℂ) * dedekindEta z)
  let T : Set ℂ := {z | Polynomial.IsRoot (Polynomial.X ^ 3 - 1 : Polynomial ℂ) z}
  have hp : (Polynomial.X ^ 3 - 1 : Polynomial ℂ) ≠ 0 := by
    intro h
    have he := congrArg (Polynomial.eval 0) h
    norm_num at he
  have hf : T.Finite := Polynomial.finite_setOf_isRoot hp
  letI : Finite T := hf.to_subtype
  have hm : Set.MapsTo R {z : ℂ | 0 < z.im} T := by
    intro z hz
    have h0 : z ≠ 0 := fun h => (ne_of_gt hz) (congrArg Complex.im h)
    have hs : (-I * z) ^ (1 / 2 : ℂ) ≠ 0 :=
      cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) h0))
    have he : R z ^ 3 = 1 := by
      dsimp only [R]
      rw [div_pow, mul_pow, dedekindEta_neg_inv_pow_three hz]
      exact div_self (mul_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ (dedekindEta_ne_zero hz)))
    simpa only [T, Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, sub_eq_zero] using he
  have hc := (convex_halfSpace_im_gt 0).isPreconnected.constant_of_mapsTo
    (T := T) continuousOn_eta_inversion_ratio hm hτ (by simp : (I : ℂ).im > 0)
  have hI : R I = 1 := by
    dsimp only [R]
    have hi : -1 / I = I := by simp [div_I]
    rw [hi]
    simp only [neg_mul, I_mul_I, neg_neg, one_cpow, one_mul]
    exact div_self (dedekindEta_ne_zero (by simp))
  exact hc.trans hI

theorem dedekindEta_neg_inv {τ : ℂ} (hτ : 0 < τ.im) :
    dedekindEta (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * dedekindEta τ := by
  exact (div_eq_one_iff_eq (mul_ne_zero
    (cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero)
      (fun h => (ne_of_gt hτ) (congrArg Complex.im h)))))
    (dedekindEta_ne_zero hτ))).mp (eta_inversion_ratio_eq_one hτ)

theorem dedekindEta_add_one_pow_twenty_four (τ : ℂ) :
    dedekindEta (τ + 1) ^ 24 = dedekindEta τ ^ 24 := by
  rw [dedekindEta_add_one, mul_pow, ← exp_nat_mul]
  have he : (24 : ℂ) * (π * I / 12) = 2 * π * I := by ring
  norm_num only [Nat.cast_ofNat]
  rw [he, exp_two_pi_mul_I, one_mul]

theorem dedekindEta_neg_inv_pow_twenty_four {τ : ℂ} (hτ : 0 < τ.im) :
    dedekindEta (-1 / τ) ^ 24 = τ ^ 12 * dedekindEta τ ^ 24 := by
  rw [dedekindEta_neg_inv hτ, mul_pow]
  have hs : ((-I * τ) ^ (1 / 2 : ℂ)) ^ 2 = -I * τ := by
    simpa only [one_div] using cpow_nat_inv_pow (-I * τ) (n := 2) two_ne_zero
  have he : ((-I * τ) ^ (1 / 2 : ℂ)) ^ 24 = τ ^ 12 := by
    calc
      _ = (((-I * τ) ^ (1 / 2 : ℂ)) ^ 2) ^ 12 := by ring
      _ = (-I * τ) ^ 12 := by rw [hs]
      _ = τ ^ 12 := by
        rw [mul_pow, neg_pow, I_pow_eq_pow_mod]
        norm_num
  rw [he]

end DirichletL

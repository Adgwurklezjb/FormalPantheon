import Analysis.LevelTwoExceptionalOrbit
import Analysis.LevelTwoOrbitRepresentatives
import Analysis.LevelTwoRootBounds

/-!
Finite alternatives for CDT author Lemma A.4.4, page 205. Meanings and
-/

namespace DirichletL

open Complex Function.Periodic
open _root_.UpperHalfPlane hiding I
open scoped MatrixGroups

theorem levelTwoHauptmodul_fiber_cases {q0 : ℝ}
    (hq0 : q0 ∈ Set.Ioo 0 (1 / 10000))
    (hv0 : levelTwoHauptmodul (q0 : ℂ) = -1 / 72)
    {q : ℂ} (hq : ‖q‖ ≤ 77 / 100) (hv : levelTwoHauptmodul q = -1 / 72) :
    q = (q0 : ℂ) ∨
      ∃ n : ℤ, n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ) ∧
        q = Function.Periodic.qParam 1
          ((Function.Periodic.invQParam 1 (q0 : ℂ) + (n : ℂ)) /
            (2 * Function.Periodic.invQParam 1 (q0 : ℂ) + (2 * (n : ℂ) + 1))) := by
  have hqne : q ≠ 0 := by
    intro h
    rw [h, levelTwoHauptmodul_zero] at hv
    norm_num at hv
  have hq0ne : (q0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hq0.1)
  have ht0 := levelTwoHauptmodul_real_preimage_height_bounds hq0 hv0
  have ht0pos : 0 < (invQParam 1 (q0 : ℂ)).im := lt_of_lt_of_le (by norm_num) ht0.1
  have htpos : 0 < (invQParam 1 q).im := by
    have hlog : Real.log ‖q‖ < 0 :=
      Real.log_neg (norm_pos_iff.mpr hqne) (hq.trans_lt (by norm_num))
    rw [im_invQParam]
    exact mul_pos_of_neg_of_neg
      (div_neg_of_neg_of_pos (by norm_num) (by positivity)) hlog
  let τ0 : ℍ := ⟨invQParam 1 (q0 : ℂ), ht0pos⟩
  let τ : ℍ := ⟨invQParam 1 q, htpos⟩
  have hτ0 : qParam 1 τ0 = (q0 : ℂ) := qParam_right_inv (by norm_num) hq0ne
  have hτ : qParam 1 τ = q := qParam_right_inv (by norm_num) hqne
  have hre : τ0.re = 0 := by
    change (invQParam 1 (q0 : ℂ)).re = 0
    simp [invQParam, ← Complex.ofReal_log hq0.1.le, Complex.mul_re, Complex.div_re]
  obtain ⟨γ, hγ, hact⟩ := levelTwoHauptmodul_exceptional_fiber_orbit
    hq0 hv0 τ0 τ hτ0 (by rw [hτ]; exact hv)
  have hnorm : ‖qParam 1 (γ • τ0 : ℍ)‖ ≤ 77 / 100 := by
    rw [hact, hτ]
    exact hq
  rcases levelTwo_qParam_orbit_cases γ hγ τ0 hre ht0 hnorm with hcentral | ⟨n, hn, heq⟩
  · exact Or.inl (by simpa only [hact, hτ, hτ0] using hcentral)
  · have hmatrix : ((levelTwoOrbitMatrix n • τ0 : ℍ) : ℂ) =
        (invQParam 1 (q0 : ℂ) + (n : ℂ)) /
          (2 * invQParam 1 (q0 : ℂ) + (2 * (n : ℂ) + 1)) := by
      simp [UpperHalfPlane.specialLinearGroup_apply, levelTwoOrbitMatrix, τ0]
    rw [hact, hτ, hmatrix] at heq
    exact Or.inr ⟨n, hn, heq⟩

end DirichletL

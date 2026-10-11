import Analysis.LevelTwoFiberCertificates.NegThree
import Analysis.LevelTwoFiberCertificates.NegTwo
import Analysis.LevelTwoFiberCertificates.NegOne
import Analysis.LevelTwoFiberCertificates.Zero
import Analysis.LevelTwoFiberCertificates.One
import Analysis.LevelTwoFiberCertificates.Two
import Analysis.LevelTwoFiniteFiber
import Analysis.ContourLocalImage
import Analysis.ContourMap

/-!
Exceptional fiber exclusions and nome identification for CDT author Lemma A.4.4, page 205.
Full meanings and the exhaustive dependency chain precede the bodies in
-/

namespace DirichletL

theorem not_mem_image_cdtContourDiskMap_levelTwo_orbit {q : ℝ}
    (hq : q ∈ Set.Ioo 0 (1 / 10000))
    (hv : levelTwoHauptmodul (q : ℂ) = -1 / 72) (n : ℤ)
    (hn : n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ)) :
    Function.Periodic.qParam 1
      ((Function.Periodic.invQParam 1 (q : ℂ) + (n : ℂ)) /
        (2 * Function.Periodic.invQParam 1 (q : ℂ) + (2 * (n : ℂ) + 1)))
      ∉ cdtContourDiskMap '' Metric.closedBall (0 : ℂ) 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [Int.cast_neg, Int.cast_ofNat] using
      LevelTwoFiberCertificates.NegThree.not_mem_image hq hv
  · simpa only [Int.cast_neg, Int.cast_ofNat] using
      LevelTwoFiberCertificates.NegTwo.not_mem_image hq hv
  · simpa only [Int.cast_neg, Int.cast_one] using
      LevelTwoFiberCertificates.NegOne.not_mem_image hq hv
  · simpa only [Int.cast_zero] using LevelTwoFiberCertificates.Zero.not_mem_image hq hv
  · simpa only [Int.cast_one] using LevelTwoFiberCertificates.One.not_mem_image hq hv
  · simpa only [Int.cast_ofNat] using LevelTwoFiberCertificates.Two.not_mem_image hq hv

theorem levelTwoHauptmodul_eq_real_preimage_of_mem_image {q0 : ℝ}
    (hq0 : q0 ∈ Set.Ioo 0 (1 / 10000))
    (hv0 : levelTwoHauptmodul (q0 : ℂ) = -1 / 72) {q : ℂ}
    (hq : q ∈ cdtContourDiskMap '' Metric.closedBall (0 : ℂ) 1)
    (hv : levelTwoHauptmodul q = -1 / 72) : q = (q0 : ℂ) := by
  have hnorm : ‖q‖ ≤ 77 / 100 := by
    obtain ⟨z, hz, rfl⟩ := hq
    exact (norm_cdtContourDiskMap_lt
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)).le
  rcases levelTwoHauptmodul_fiber_cases hq0 hv0 hnorm hv with heq | ⟨n, hn, heq⟩
  · exact heq
  · exact (not_mem_image_cdtContourDiskMap_levelTwo_orbit hq0 hv0 n hn
      (by simpa only [← heq] using hq)).elim

end DirichletL

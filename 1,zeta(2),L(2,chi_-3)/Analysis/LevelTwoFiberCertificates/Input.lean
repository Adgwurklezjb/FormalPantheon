import Analysis.LevelTwoOrbitEnclosure
import Analysis.LevelTwoRootRefinement

/-!
Exact exceptional-fiber certificate for CDT author Lemma A.4.4, page 205.
Complete meanings and data precede these bodies in
-/

namespace DirichletL.LevelTwoFiberCertificates

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Common integer scale for the six exceptional-fiber certificates. -/
def scale : ℕ := 2 ^ 120

private def rootInterval : NonemptyInterval ℤ := (NonemptyInterval.pure (72021514542567332022189805138888 : ℤ) ⊔ NonemptyInterval.pure (72021514542580624302147654297618 : ℤ))

/-- Complete proposed height interval, interpreted by the checked logarithm below. -/
def height : NonemptyInterval ℤ := (NonemptyInterval.pure (2078117604311593021768366914187824654 : ℤ) ⊔ NonemptyInterval.pure (2078117604311639719108962714088150716 : ℤ))

private theorem root_mem {q : ℝ}
    (hq : q ∈ Set.Icc (5418296542877 / 100000000000000000)
      (5418296542878 / 100000000000000000)) :
    q ∈ ScaledInterval.denote scale rootInterval := by
  have hl : (rootInterval.fst : ℝ) / scale ≤
      5418296542877 / 100000000000000000 := by norm_num [rootInterval, scale]
  have hu : (5418296542878 / 100000000000000000 : ℝ) ≤
      (rootInterval.snd : ℝ) / scale := by norm_num [rootInterval, scale]
  exact ⟨hl.trans hq.1, hq.2.trans hu⟩

private theorem height_check :
    ScaledRectangle.levelTwoHeight? scale rootInterval = some height := by decide +kernel

theorem invQParam_mem {q : ℝ} (hq : q ∈ Set.Ioo 0 (1 / 10000))
    (hv : levelTwoHauptmodul (q : ℂ) = -1 / 72) :
    Function.Periodic.invQParam 1 (q : ℂ) ∈
      ScaledRectangle.denote scale (0, height) := by
  exact ScaledRectangle.levelTwoHeight?_mem (by norm_num [scale]) height_check hq.1
    (root_mem (levelTwoHauptmodul_real_preimage_refined_bounds hq hv))

end DirichletL.LevelTwoFiberCertificates

import Analysis.LevelTwoFiberCertificates.Input
import Analysis.ContourReverseEnclosure

/-!
Exact exceptional-fiber certificate for CDT author Lemma A.4.4, page 205.
Complete meanings and data precede these bodies in
-/

namespace DirichletL.LevelTwoFiberCertificates.Zero

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def nome : ScaledRectangle := ((NonemptyInterval.pure (-511705117369393079626434197646262762 : ℤ) ⊔ NonemptyInterval.pure (-511705117362211790137427993159357086 : ℤ)), (NonemptyInterval.pure (153542136291246688435328951482278316 : ℤ) ⊔ NonemptyInterval.pure (153542136298465536252426601665663653 : ℤ)))

private def roots : Fin 4 → ScaledRectangle.RootCertificate := ![⟨(886488097611958336654080530124738298, 886493257192637434276844709014338636), (1085511282053574840179655515720309283, 1085514431983666684312580321670844367)⟩,
    ⟨(283802537023662927546355893069056879, 283802698915034775543923523722031674), (614192896890541954831796085860146189, 614193071491197476914887653833354752)⟩,
    ⟨(12942308499129826226324008414283, 12942439996648153348251601216634), (3447472149093904275565689135128557, 3447498854322621379366564085880965)⟩,
    ⟨(125062826790911698364578972978771599, 125062826841122676410267046956309940), (384528142984609405380324471775252483, 384528143060978775199398085701584871)⟩]

private def reverse : ScaledRectangle := ((NonemptyInterval.pure (-264850219983189035151438980129347948 : ℤ) ⊔ NonemptyInterval.pure (-264836609440065765920507751717408793 : ℤ)), (NonemptyInterval.pure (1298690793885691587585390121753704048 : ℤ) ⊔ NonemptyInterval.pure (1298704273831605480078802501022339026 : ℤ)))

private theorem nome_check :
    ScaledRectangle.levelTwoNome? scale (0) (0) height = some nome := by decide +kernel

private theorem reverse_check :
    ScaledRectangle.cdtContourReverseWithRoots? scale nome roots = some reverse := by decide +kernel

theorem not_mem_image {q : ℝ} (hq : q ∈ Set.Ioo 0 (1 / 10000))
    (hv : levelTwoHauptmodul (q : ℂ) = -1 / 72) :
    Function.Periodic.qParam 1
      ((Function.Periodic.invQParam 1 (q : ℂ) + (0 : ℂ)) /
        (2 * Function.Periodic.invQParam 1 (q : ℂ) + (2 * (0 : ℂ) + 1)))
      ∉ cdtContourDiskMap '' Metric.closedBall (0 : ℂ) 1 := by
  have hD : 0 < scale := by norm_num [scale]
  have hn := ScaledRectangle.levelTwoNome?_mem hD (0) (0) nome_check
    (invQParam_mem hq hv)
  have hr := ScaledRectangle.cdtContourReverseWithRoots?_mem hD reverse_check hn
  have h := ScaledRectangle.not_mem_image_cdtContourDiskMap_of_reverse_enclosure
    hD hr (by decide +kernel)
  simpa only [Int.cast_neg, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using h

end DirichletL.LevelTwoFiberCertificates.Zero

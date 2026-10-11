import Analysis.LevelTwoFiberCertificates.Input
import Analysis.ContourReverseEnclosure

/-!
Exact exceptional-fiber certificate for CDT author Lemma A.4.4, page 205.
Complete meanings and data precede these bodies in
-/

namespace DirichletL.LevelTwoFiberCertificates.NegTwo

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def nome : ScaledRectangle := ((NonemptyInterval.pure (-690599193558147101686348172375053333 : ℤ) ⊔ NonemptyInterval.pure (-690599193553371276728264205118081703 : ℤ)), (NonemptyInterval.pure (-379012712884185625318970807448308570 : ℤ) ⊔ NonemptyInterval.pure (-379012712879411166653149420818421618 : ℤ)))

private def roots : Fin 4 → ScaledRectangle.RootCertificate := ![⟨(140046790846856027487272015723575, 140048555164843348652626710072945), (13619132551750268955517272434604193, 13619214965425634643185258302168393)⟩,
    ⟨(89803485740443223237516562292881555, 89803488870282462820598394269158947), (339302850709158412866036158888401726, 339302856133250131414827150352523450)⟩,
    ⟨(374171764494377008587325977431941107, 374171765820913413747270771743196857), (685221747790123696382131262757322032, 685221748912588737138972626490502413)⟩,
    ⟨(427877113052798906502324591399771739, 427877113186764788595685991887640334), (723249331517437887822880553071606962, 723249331623654071024788751589274107)⟩]

private def reverse : ScaledRectangle := ((NonemptyInterval.pure (-1327309403758205908088304980931936928 : ℤ) ⊔ NonemptyInterval.pure (-1327309116508934002006680792231624187 : ℤ)), (NonemptyInterval.pure (27201810558471164584655518640355725 : ℤ) ⊔ NonemptyInterval.pure (27201979561892483434163075824255550 : ℤ)))

private theorem nome_check :
    ScaledRectangle.levelTwoNome? scale (-2) (1) height = some nome := by decide +kernel

private theorem reverse_check :
    ScaledRectangle.cdtContourReverseWithRoots? scale nome roots = some reverse := by decide +kernel

theorem not_mem_image {q : ℝ} (hq : q ∈ Set.Ioo 0 (1 / 10000))
    (hv : levelTwoHauptmodul (q : ℂ) = -1 / 72) :
    Function.Periodic.qParam 1
      ((Function.Periodic.invQParam 1 (q : ℂ) + (-2 : ℂ)) /
        (2 * Function.Periodic.invQParam 1 (q : ℂ) + (2 * (-2 : ℂ) + 1)))
      ∉ cdtContourDiskMap '' Metric.closedBall (0 : ℂ) 1 := by
  have hD : 0 < scale := by norm_num [scale]
  have hn := ScaledRectangle.levelTwoNome?_mem hD (-2) (1) nome_check
    (invQParam_mem hq hv)
  have hr := ScaledRectangle.cdtContourReverseWithRoots?_mem hD reverse_check hn
  have h := ScaledRectangle.not_mem_image_cdtContourDiskMap_of_reverse_enclosure
    hD hr (by decide +kernel)
  simpa only [Int.cast_neg, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using h

end DirichletL.LevelTwoFiberCertificates.NegTwo

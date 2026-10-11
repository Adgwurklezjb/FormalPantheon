import Analysis.LevelTwoFiberCertificates.Input
import Analysis.ContourReverseEnclosure

/-!
Exact exceptional-fiber certificate for CDT author Lemma A.4.4, page 205.
Complete meanings and data precede these bodies in
-/

namespace DirichletL.LevelTwoFiberCertificates.Two

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def nome : ScaledRectangle := ((NonemptyInterval.pure (-901640321282330532868176115067875595 : ℤ) ⊔ NonemptyInterval.pure (-901640321280262766465386960032094330 : ℤ)), (NonemptyInterval.pure (437409479288675353093036729143995778 : ℤ) ⊔ NonemptyInterval.pure (437409479290741299471913394067139089 : ℤ)))

private def roots : Fin 4 → ScaledRectangle.RootCertificate := ![⟨(398182455169930658381677071442971613, 398182455175564713566762724089814488), (727513067180587486289373802216728378, 727513067185734019065585886982405141)⟩,
    ⟨(85328021418269661107239526326769624, 85328021418514029728125862896311139), (336779441530114855034241342951864399, 336779441530597034672173127412217642)⟩,
    ⟨(119037686846925229721242337001465503, 119037686847145560237369470857102101), (397779073619718200147575181555196530, 397779073620086125144181517731013478)⟩,
    ⟨(23035276921296204333896620087219404, 23035276921880747649212105442983454), (174964262111374240499181711018524548, 174964262113563531986953546508877844)⟩]

private def reverse : ScaledRectangle := ((NonemptyInterval.pure (-716379856076330123260356766928374732 : ℤ) ⊔ NonemptyInterval.pure (-716379856052815337937072550481223743 : ℤ)), (NonemptyInterval.pure (1119549331617007941220112135322048781 : ℤ) ⊔ NonemptyInterval.pure (1119549331638893756828970986040880744 : ℤ)))

private theorem nome_check :
    ScaledRectangle.levelTwoNome? scale (2) (0) height = some nome := by decide +kernel

private theorem reverse_check :
    ScaledRectangle.cdtContourReverseWithRoots? scale nome roots = some reverse := by decide +kernel

theorem not_mem_image {q : ℝ} (hq : q ∈ Set.Ioo 0 (1 / 10000))
    (hv : levelTwoHauptmodul (q : ℂ) = -1 / 72) :
    Function.Periodic.qParam 1
      ((Function.Periodic.invQParam 1 (q : ℂ) + (2 : ℂ)) /
        (2 * Function.Periodic.invQParam 1 (q : ℂ) + (2 * (2 : ℂ) + 1)))
      ∉ cdtContourDiskMap '' Metric.closedBall (0 : ℂ) 1 := by
  have hD : 0 < scale := by norm_num [scale]
  have hn := ScaledRectangle.levelTwoNome?_mem hD (2) (0) nome_check
    (invQParam_mem hq hv)
  have hr := ScaledRectangle.cdtContourReverseWithRoots?_mem hD reverse_check hn
  have h := ScaledRectangle.not_mem_image_cdtContourDiskMap_of_reverse_enclosure
    hD hr (by decide +kernel)
  simpa only [Int.cast_neg, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using h

end DirichletL.LevelTwoFiberCertificates.Two

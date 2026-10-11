import Analysis.LevelTwoFiberCertificates.Input
import Analysis.ContourReverseEnclosure

/-!
Exact exceptional-fiber certificate for CDT author Lemma A.4.4, page 205.
Complete meanings and data precede these bodies in
-/

namespace DirichletL.LevelTwoFiberCertificates.NegOne

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def nome : ScaledRectangle := ((NonemptyInterval.pure (-511705117371055743625668069931446796 : ℤ) ⊔ NonemptyInterval.pure (-511705117360549126138194149943049091 : ℤ)), (NonemptyInterval.pure (-153542136300118991982159438678074674 : ℤ) ⊔ NonemptyInterval.pure (-153542136289593232705596133024496825 : ℤ)))

private def roots : Fin 4 → ScaledRectangle.RootCertificate := ![⟨(87323725751748610315014578987017873, 87325633502233220311856075569480810), (340694896808724016490882652155270587, 340698614932040681292506829842043387)⟩,
    ⟨(22108581136332910397619118168956, 22117149162541205568584667758812), (5410115235102159164054161107607084, 5411127811698595430410253545666132)⟩,
    ⟨(262942786235933574028971147109977133, 262942788605657394263183051551702299), (472603067654360638350108193261300652, 472603070683882317228666940296050240)⟩,
    ⟨(352289830325696122135248755399139426, 352289830493012891142499883192633183), (505488086892280447877761875013141235, 505488087103300236504130324749390482)⟩]

private def reverse : ScaledRectangle := ((NonemptyInterval.pure (-1164761334459632031955115564075899965 : ℤ) ⊔ NonemptyInterval.pure (-1164745581959043006886113974884110614 : ℤ)), (NonemptyInterval.pure (639057635753728774005262103208154312 : ℤ) ⊔ NonemptyInterval.pure (639069959027034790878366471541332066 : ℤ)))

private theorem nome_check :
    ScaledRectangle.levelTwoNome? scale (-1) (1) height = some nome := by decide +kernel

private theorem reverse_check :
    ScaledRectangle.cdtContourReverseWithRoots? scale nome roots = some reverse := by decide +kernel

theorem not_mem_image {q : ℝ} (hq : q ∈ Set.Ioo 0 (1 / 10000))
    (hv : levelTwoHauptmodul (q : ℂ) = -1 / 72) :
    Function.Periodic.qParam 1
      ((Function.Periodic.invQParam 1 (q : ℂ) + (-1 : ℂ)) /
        (2 * Function.Periodic.invQParam 1 (q : ℂ) + (2 * (-1 : ℂ) + 1)))
      ∉ cdtContourDiskMap '' Metric.closedBall (0 : ℂ) 1 := by
  have hD : 0 < scale := by norm_num [scale]
  have hn := ScaledRectangle.levelTwoNome?_mem hD (-1) (1) nome_check
    (invQParam_mem hq hv)
  have hr := ScaledRectangle.cdtContourReverseWithRoots?_mem hD reverse_check hn
  have h := ScaledRectangle.not_mem_image_cdtContourDiskMap_of_reverse_enclosure
    hD hr (by decide +kernel)
  simpa only [Int.cast_neg, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using h

end DirichletL.LevelTwoFiberCertificates.NegOne

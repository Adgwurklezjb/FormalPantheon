import Analysis.LevelTwoFiberCertificates.Input
import Analysis.ContourReverseEnclosure

/-!
Exact exceptional-fiber certificate for CDT author Lemma A.4.4, page 205.
Complete meanings and data precede these bodies in
-/

namespace DirichletL.LevelTwoFiberCertificates.One

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def nome : ScaledRectangle := ((NonemptyInterval.pure (-690599193557623854350198793733925237 : ℤ) ⊔ NonemptyInterval.pure (-690599193553894524064413584329900362 : ℤ)), (NonemptyInterval.pure (379012712879932595974824873696081049 : ℤ) ⊔ NonemptyInterval.pure (379012712883664195997295344924423445 : ℤ)))

private def roots : Fin 4 → ScaledRectangle.RootCertificate := ![⟨(2759440302312168331177258290067232204, 2759440715069751299859574160677806275), (1915173647556323518595829664933202813, 1915173790368723485427261962172499170)⟩,
    ⟨(992804624557566032200070001503320209, 992804631173579745791918358858306739), (1148761206575135182356921367138192455, 1148761210391788701015175133013471431)⟩,
    ⟨(142005623394186162504754074045522978, 142005623526140660910808290326282627), (434456667095390027014863305912273491, 434456667296162603812673618851214922)⟩,
    ⟨(368421999347216414967789460371294, 368422005640324665466329831611349), (21483804611611045584664726171780969, 21483804786017987407632887402102847)⟩]

private def reverse : ScaledRectangle := ((NonemptyInterval.pure (463616973913659152330084310287703297 : ℤ) ⊔ NonemptyInterval.pure (463617419487689919627495723999846956 : ℤ)), (NonemptyInterval.pure (1241643894128616305708639471481740994 : ℤ) ⊔ NonemptyInterval.pure (1241644324280503044504235295020762630 : ℤ)))

private theorem nome_check :
    ScaledRectangle.levelTwoNome? scale (1) (0) height = some nome := by decide +kernel

private theorem reverse_check :
    ScaledRectangle.cdtContourReverseWithRoots? scale nome roots = some reverse := by decide +kernel

theorem not_mem_image {q : ℝ} (hq : q ∈ Set.Ioo 0 (1 / 10000))
    (hv : levelTwoHauptmodul (q : ℂ) = -1 / 72) :
    Function.Periodic.qParam 1
      ((Function.Periodic.invQParam 1 (q : ℂ) + (1 : ℂ)) /
        (2 * Function.Periodic.invQParam 1 (q : ℂ) + (2 * (1 : ℂ) + 1)))
      ∉ cdtContourDiskMap '' Metric.closedBall (0 : ℂ) 1 := by
  have hD : 0 < scale := by norm_num [scale]
  have hn := ScaledRectangle.levelTwoNome?_mem hD (1) (0) nome_check
    (invQParam_mem hq hv)
  have hr := ScaledRectangle.cdtContourReverseWithRoots?_mem hD reverse_check hn
  have h := ScaledRectangle.not_mem_image_cdtContourDiskMap_of_reverse_enclosure
    hD hr (by decide +kernel)
  simpa only [Int.cast_neg, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using h

end DirichletL.LevelTwoFiberCertificates.One

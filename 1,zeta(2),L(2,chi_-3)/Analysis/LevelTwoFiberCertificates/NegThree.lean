import Analysis.LevelTwoFiberCertificates.Input
import Analysis.ContourReverseEnclosure

/-!
Exact exceptional-fiber certificate for CDT author Lemma A.4.4, page 205.
Complete meanings and data precede these bodies in
-/

namespace DirichletL.LevelTwoFiberCertificates.NegThree

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def nome : ScaledRectangle := ((NonemptyInterval.pure (-901640321282528971124017821869126164 : ℤ) ⊔ NonemptyInterval.pure (-901640321280064328209545252957273278 : ℤ)), (NonemptyInterval.pure (-437409479290939245542608627448248507 : ℤ) ⊔ NonemptyInterval.pure (-437409479288477407022341498558190139 : ℤ)))

private def roots : Fin 4 → ScaledRectangle.RootCertificate := ![⟨(3056266286407137151181600929708800, 3056266317784252812341466295986225), (63732809003066919229542220068358591, 63732809326314808837661503578082459)⟩,
    ⟨(93847398920990369808807553467207462, 93847399172919732616892353613015200), (353164867697154176579908074933063809, 353164868166142116821454453893174124)⟩,
    ⟨(340394918648947615954043220647551881, 340394918889509601193130350260460047), (672530533447488212606606106365091873, 672530533681342768541109230280011435)⟩,
    ⟨(367351838345030633776396472353680546, 367351838381442648243737048316059532), (698576836512757336752792277547135682, 698576836546673482197529900652864619)⟩]

private def reverse : ScaledRectangle := ((NonemptyInterval.pure (-1321587913572236946481338090059032624 : ℤ) ⊔ NonemptyInterval.pure (-1321587912185792256117042581092301159 : ℤ)), (NonemptyInterval.pure (-127025043015873387295109519873756299 : ℤ) ⊔ NonemptyInterval.pure (-127025042273541513792773415501245040 : ℤ)))

private theorem nome_check :
    ScaledRectangle.levelTwoNome? scale (-3) (1) height = some nome := by decide +kernel

private theorem reverse_check :
    ScaledRectangle.cdtContourReverseWithRoots? scale nome roots = some reverse := by decide +kernel

theorem not_mem_image {q : ℝ} (hq : q ∈ Set.Ioo 0 (1 / 10000))
    (hv : levelTwoHauptmodul (q : ℂ) = -1 / 72) :
    Function.Periodic.qParam 1
      ((Function.Periodic.invQParam 1 (q : ℂ) + (-3 : ℂ)) /
        (2 * Function.Periodic.invQParam 1 (q : ℂ) + (2 * (-3 : ℂ) + 1)))
      ∉ cdtContourDiskMap '' Metric.closedBall (0 : ℂ) 1 := by
  have hD : 0 < scale := by norm_num [scale]
  have hn := ScaledRectangle.levelTwoNome?_mem hD (-3) (1) nome_check
    (invQParam_mem hq hv)
  have hr := ScaledRectangle.cdtContourReverseWithRoots?_mem hD reverse_check hn
  have h := ScaledRectangle.not_mem_image_cdtContourDiskMap_of_reverse_enclosure
    hD hr (by decide +kernel)
  simpa only [Int.cast_neg, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using h

end DirichletL.LevelTwoFiberCertificates.NegThree

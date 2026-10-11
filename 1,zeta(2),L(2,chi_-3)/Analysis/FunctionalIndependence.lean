import Analysis.Hauptmodul

/-!
Formal coordinate series from CDT v2 Section 11.1, Lemma `defabc` and
Proposition `functionsH`. This file proves algebraic coefficient and
denominator facts only; it does not assert analytic continuation.
-/

namespace DirichletL

/-- The canonical integer compositional inverse of the formal Hauptmodul. -/
noncomputable def hauptmodulInverse : PowerSeries ℤ := reversion hauptmodul

theorem constantCoeff_hauptmodulInverse :
    PowerSeries.constantCoeff (R := ℤ) hauptmodulInverse = 0 := by
  exact constantCoeff_reversion hauptmodul

theorem coeff_one_hauptmodulInverse :
    PowerSeries.coeff (R := ℤ) 1 hauptmodulInverse = 1 := by
  exact coeff_one_reversion hauptmodul

private theorem coeff_two_mul_int (f g : PowerSeries ℤ) :
    PowerSeries.coeff (R := ℤ) 2 (f * g) =
      PowerSeries.coeff (R := ℤ) 0 f * PowerSeries.coeff (R := ℤ) 2 g +
        PowerSeries.coeff (R := ℤ) 1 f * PowerSeries.coeff (R := ℤ) 1 g +
          PowerSeries.coeff (R := ℤ) 2 f * PowerSeries.coeff (R := ℤ) 0 g := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_eq_map, Finset.sum_map]
  norm_num [Finset.sum_range_succ]

private theorem coeff_three_mul_int (f g : PowerSeries ℤ) :
    PowerSeries.coeff (R := ℤ) 3 (f * g) =
      PowerSeries.coeff (R := ℤ) 0 f * PowerSeries.coeff (R := ℤ) 3 g +
        PowerSeries.coeff (R := ℤ) 1 f * PowerSeries.coeff (R := ℤ) 2 g +
          PowerSeries.coeff (R := ℤ) 2 f * PowerSeries.coeff (R := ℤ) 1 g +
            PowerSeries.coeff (R := ℤ) 3 f * PowerSeries.coeff (R := ℤ) 0 g := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_eq_map, Finset.sum_map]
  norm_num [Finset.sum_range_succ]

private theorem coeff_two_hauptmodul_pow_two :
    PowerSeries.coeff (R := ℤ) 2 (hauptmodul ^ 2) = 1 := by
  rw [show hauptmodul ^ 2 = hauptmodul * hauptmodul by ring, coeff_two_mul_int]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_hauptmodul,
    coeff_one_hauptmodul]

private theorem coeff_one_hauptmodul_pow_two :
    PowerSeries.coeff (R := ℤ) 1 (hauptmodul ^ 2) = 0 := by
  rw [show hauptmodul ^ 2 = hauptmodul * hauptmodul by ring,
    PowerSeries.coeff_one_mul]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_hauptmodul,
    coeff_one_hauptmodul]

private theorem coeff_three_hauptmodul_pow_two :
    PowerSeries.coeff (R := ℤ) 3 (hauptmodul ^ 2) = -8 := by
  rw [show hauptmodul ^ 2 = hauptmodul * hauptmodul by ring, coeff_three_mul_int]
  norm_num [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_hauptmodul, coeff_one_hauptmodul, coeff_two_hauptmodul,
    coeff_three_hauptmodul]

private theorem coeff_three_hauptmodul_pow_three :
    PowerSeries.coeff (R := ℤ) 3 (hauptmodul ^ 3) = 1 := by
  rw [show hauptmodul ^ 3 = hauptmodul ^ 2 * hauptmodul by ring,
    coeff_three_mul_int]
  norm_num [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_hauptmodul, coeff_one_hauptmodul, coeff_two_hauptmodul,
    coeff_three_hauptmodul, coeff_one_hauptmodul_pow_two,
    coeff_two_hauptmodul_pow_two]

theorem subst_hauptmodul_hauptmodulInverse :
    MvPowerSeries.subst (fun (_ : Unit) => hauptmodul) hauptmodulInverse =
      PowerSeries.X := by
  exact subst_reversion hauptmodul constantCoeff_hauptmodul coeff_one_hauptmodul

theorem subst_hauptmodulInverse_hauptmodul :
    MvPowerSeries.subst (fun (_ : Unit) => hauptmodulInverse) hauptmodul =
      PowerSeries.X := by
  exact reversion_subst hauptmodul constantCoeff_hauptmodul coeff_one_hauptmodul

/-- The degree-two inverse coefficient from CDT v2 Section 11.1, equation
`invert`, derived from the formal substitution identity. -/
theorem coeff_two_hauptmodulInverse :
    PowerSeries.coeff (R := ℤ) 2 hauptmodulInverse = 4 := by
  have h2 := congrArg (PowerSeries.coeff (R := ℤ) 2) subst_hauptmodul_hauptmodulInverse
  rw [coeff_subst_eq_sum hauptmodulInverse hauptmodul constantCoeff_hauptmodul 2] at h2
  norm_num [Finset.sum_range_succ, PowerSeries.coeff_X,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_hauptmodul,
    constantCoeff_hauptmodulInverse, coeff_one_hauptmodul,
    coeff_one_hauptmodulInverse, coeff_two_hauptmodul,
    coeff_two_hauptmodul_pow_two, pow_zero, pow_one] at h2
  linarith

/-- The degree-three inverse coefficient from CDT v2 Section 11.1, equation
`invert`, derived from the formal substitution identity. -/
theorem coeff_three_hauptmodulInverse :
    PowerSeries.coeff (R := ℤ) 3 hauptmodulInverse = 22 := by
  have h2 : PowerSeries.coeff (R := ℤ) 2 hauptmodulInverse = 4 :=
    coeff_two_hauptmodulInverse
  have h3 := congrArg (PowerSeries.coeff (R := ℤ) 3) subst_hauptmodul_hauptmodulInverse
  rw [coeff_subst_eq_sum hauptmodulInverse hauptmodul constantCoeff_hauptmodul 3] at h3
  norm_num [Finset.sum_range_succ, PowerSeries.coeff_X,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_hauptmodul,
    constantCoeff_hauptmodulInverse, coeff_one_hauptmodul,
    coeff_one_hauptmodulInverse, coeff_two_hauptmodul, coeff_three_hauptmodul,
    coeff_one_hauptmodul_pow_two, coeff_two_hauptmodul_pow_two,
    coeff_three_hauptmodul_pow_two, coeff_three_hauptmodul_pow_three,
    pow_zero, pow_one] at h3
  nlinarith [h2]

/-- The formal A-series in the Hauptmodul coordinate. -/
noncomputable def hA : PowerSeries ℚ := zagierGenerating

/-- The formal B-series obtained by substituting the integer inverse. -/
noncomputable def hB : PowerSeries ℚ :=
  zagierGenerating *
    MvPowerSeries.subst
      (fun (_ : Unit) => PowerSeries.map (Int.castRingHom ℚ) hauptmodulInverse)
      (PowerSeries.mk betaCoeff)

/-- The formal C-series obtained by substituting the integer inverse. -/
noncomputable def hC : PowerSeries ℚ :=
  zagierGenerating *
    MvPowerSeries.subst
      (fun (_ : Unit) => PowerSeries.map (Int.castRingHom ℚ) hauptmodulInverse)
      (PowerSeries.mk gammaCoeff)

theorem coeff_subst_zero {f g : PowerSeries ℚ}
    (hg : PowerSeries.constantCoeff (R := ℚ) g = 0) :
    PowerSeries.coeff (R := ℚ) 0
        (MvPowerSeries.subst (fun (_ : Unit) => g) f) =
      PowerSeries.coeff (R := ℚ) 0 f := by
  rw [coeff_subst_eq_sum f g hg 0]
  simp

theorem coeff_subst_one {f g : PowerSeries ℚ}
    (hg : PowerSeries.constantCoeff (R := ℚ) g = 0) :
    PowerSeries.coeff (R := ℚ) 1
        (MvPowerSeries.subst (fun (_ : Unit) => g) f) =
      PowerSeries.coeff (R := ℚ) 1 f * PowerSeries.coeff (R := ℚ) 1 g := by
  rw [coeff_subst_eq_sum f g hg 1]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_pow_self_of_constantCoeff_zero g hg]

theorem coeff_subst_two {f g : PowerSeries ℚ}
    (hg : PowerSeries.constantCoeff (R := ℚ) g = 0) :
    PowerSeries.coeff (R := ℚ) 2
        (MvPowerSeries.subst (fun (_ : Unit) => g) f) =
      PowerSeries.coeff (R := ℚ) 1 f * PowerSeries.coeff (R := ℚ) 2 g +
        PowerSeries.coeff (R := ℚ) 2 f * (PowerSeries.coeff (R := ℚ) 1 g) ^ 2 := by
  rw [coeff_subst_eq_sum f g hg 2]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    pow_zero, one_mul, PowerSeries.coeff_one,
    coeff_pow_self_of_constantCoeff_zero g hg]
  simp only [if_neg (by norm_num : ¬(2 : ℕ) = 0)]
  ring

theorem betaCoeff_one : betaCoeff 1 = 1 := by
  rw [betaCoeff, betaNumerator_one]
  norm_num

theorem betaCoeff_two : betaCoeff 2 = -5 / 4 := by
  rw [betaCoeff, betaNumerator_two]
  norm_num

theorem gammaCoeff_one : gammaCoeff 1 = 1 := by
  norm_num [gammaCoeff, gammaNumerator, chiMinusThreeInt_one]

theorem gammaCoeff_two : gammaCoeff 2 = -1 := by
  norm_num [gammaCoeff, gammaNumerator, chiMinusThreeInt_one,
    chiMinusThreeInt_two]

theorem hA_coeff_zero : PowerSeries.coeff (R := ℚ) 0 hA = 1 := by
  simp [hA, zagierGenerating, generatingSeries, zagierC_zero]

theorem hA_coeff_one : PowerSeries.coeff (R := ℚ) 1 hA = 3 := by
  simp [hA, zagierGenerating, generatingSeries, zagierC_one]

theorem hA_coeff_two : PowerSeries.coeff (R := ℚ) 2 hA = 15 := by
  simp [hA, zagierGenerating, generatingSeries, zagierC_two]

theorem hB_constantCoeff :
    PowerSeries.constantCoeff (R := ℚ) hB = 0 := by
  have hgq : PowerSeries.constantCoeff (R := ℚ)
      (PowerSeries.map (Int.castRingHom ℚ) hauptmodulInverse) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      congrArg (fun z : ℤ => (z : ℚ)) constantCoeff_hauptmodulInverse
  have hs : PowerSeries.coeff (R := ℚ) 0
      (MvPowerSeries.subst
        (fun (_ : Unit) => PowerSeries.map (Int.castRingHom ℚ) hauptmodulInverse)
        (PowerSeries.mk betaCoeff)) = betaCoeff 0 := by
    simpa only [PowerSeries.coeff_mk] using
      (coeff_subst_zero (f := PowerSeries.mk betaCoeff)
        (g := PowerSeries.map (Int.castRingHom ℚ) hauptmodulInverse) hgq)
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hB]
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.antidiagonal_zero]
  simp [hA, zagierGenerating, generatingSeries, hs, betaCoeff_zero]

theorem hC_constantCoeff :
    PowerSeries.constantCoeff (R := ℚ) hC = 0 := by
  have hgq : PowerSeries.constantCoeff (R := ℚ)
      (PowerSeries.map (Int.castRingHom ℚ) hauptmodulInverse) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      congrArg (fun z : ℤ => (z : ℚ)) constantCoeff_hauptmodulInverse
  have hs : PowerSeries.coeff (R := ℚ) 0
      (MvPowerSeries.subst
        (fun (_ : Unit) => PowerSeries.map (Int.castRingHom ℚ) hauptmodulInverse)
        (PowerSeries.mk gammaCoeff)) = gammaCoeff 0 := by
    simpa only [PowerSeries.coeff_mk] using
      (coeff_subst_zero (f := PowerSeries.mk gammaCoeff)
        (g := PowerSeries.map (Int.castRingHom ℚ) hauptmodulInverse) hgq)
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hC]
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.antidiagonal_zero]
  simp [hA, zagierGenerating, generatingSeries, hs, gammaCoeff]

theorem hB_coeff_one : PowerSeries.coeff (R := ℚ) 1 hB = 1 := by
  have hgq : PowerSeries.constantCoeff (R := ℚ)
      (PowerSeries.map (Int.castRingHom ℚ) hauptmodulInverse) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      congrArg (fun z : ℤ => (z : ℚ)) constantCoeff_hauptmodulInverse
  rw [hB, PowerSeries.coeff_one_mul]
  rw [coeff_subst_one hgq]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [coeff_subst_zero hgq]
  simp [hA, zagierGenerating, generatingSeries, betaCoeff_one,
    PowerSeries.coeff_map, coeff_one_hauptmodulInverse, betaCoeff_zero,
    zagierC_zero]

theorem hC_coeff_one : PowerSeries.coeff (R := ℚ) 1 hC = 1 := by
  have hgq : PowerSeries.constantCoeff (R := ℚ)
      (PowerSeries.map (Int.castRingHom ℚ) hauptmodulInverse) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      congrArg (fun z : ℤ => (z : ℚ)) constantCoeff_hauptmodulInverse
  rw [hC, PowerSeries.coeff_one_mul]
  rw [coeff_subst_one hgq]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [coeff_subst_zero hgq]
  simp [hA, zagierGenerating, generatingSeries, gammaCoeff_one,
    PowerSeries.coeff_map, coeff_one_hauptmodulInverse, gammaCoeff,
    gammaNumerator, zagierC_zero, chiMinusThreeInt_one,
    chiMinusThreeInt_two]

theorem coeff_mul_two (f g : PowerSeries ℚ) :
    PowerSeries.coeff (R := ℚ) 2 (f * g) =
      PowerSeries.coeff (R := ℚ) 0 f * PowerSeries.coeff (R := ℚ) 2 g +
        PowerSeries.coeff (R := ℚ) 1 f * PowerSeries.coeff (R := ℚ) 1 g +
          PowerSeries.coeff (R := ℚ) 2 f * PowerSeries.coeff (R := ℚ) 0 g := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_eq_map, Finset.sum_map]
  norm_num [Finset.sum_range_succ]

theorem hB_sub_hC_coeff_two :
    PowerSeries.coeff (R := ℚ) 2 (hB - hC) = -(1 / 4 : ℚ) := by
  let gq : PowerSeries ℚ :=
    PowerSeries.map (Int.castRingHom ℚ) hauptmodulInverse
  have hgq : PowerSeries.constantCoeff (R := ℚ) gq = 0 := by
    change PowerSeries.constantCoeff (R := ℚ)
      (PowerSeries.map (Int.castRingHom ℚ) hauptmodulInverse) = 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      congrArg (fun z : ℤ => (z : ℚ)) constantCoeff_hauptmodulInverse
  have hgq1 : PowerSeries.coeff (R := ℚ) 1 gq = 1 := by
    simp [gq, PowerSeries.coeff_map, coeff_one_hauptmodulInverse]
  have hβ0 : PowerSeries.coeff (R := ℚ) 0
      (MvPowerSeries.subst (fun (_ : Unit) => gq) (PowerSeries.mk betaCoeff)) = 0 := by
    rw [coeff_subst_zero hgq]
    simp [betaCoeff_zero]
  have hγ0 : PowerSeries.coeff (R := ℚ) 0
      (MvPowerSeries.subst (fun (_ : Unit) => gq) (PowerSeries.mk gammaCoeff)) = 0 := by
    rw [coeff_subst_zero hgq]
    simp [gammaCoeff]
  have hβ1 : PowerSeries.coeff (R := ℚ) 1
      (MvPowerSeries.subst (fun (_ : Unit) => gq) (PowerSeries.mk betaCoeff)) = 1 := by
    rw [coeff_subst_one hgq]
    simp [betaCoeff_one, PowerSeries.coeff_mk, hgq1]
  have hγ1 : PowerSeries.coeff (R := ℚ) 1
      (MvPowerSeries.subst (fun (_ : Unit) => gq) (PowerSeries.mk gammaCoeff)) = 1 := by
    rw [coeff_subst_one hgq]
    simp [gammaCoeff_one, PowerSeries.coeff_mk, hgq1]
  have hβ2 := coeff_subst_two (f := PowerSeries.mk betaCoeff) (g := gq) hgq
  have hγ2 := coeff_subst_two (f := PowerSeries.mk gammaCoeff) (g := gq) hgq
  have hβ2' : PowerSeries.coeff (R := ℚ) 2
      (MvPowerSeries.subst (fun (_ : Unit) => gq) (PowerSeries.mk betaCoeff)) =
      PowerSeries.coeff (R := ℚ) 2 gq - 5 / 4 := by
    simp only [PowerSeries.coeff_mk, betaCoeff_one, betaCoeff_two, hgq1] at hβ2
    linarith
  have hγ2' : PowerSeries.coeff (R := ℚ) 2
      (MvPowerSeries.subst (fun (_ : Unit) => gq) (PowerSeries.mk gammaCoeff)) =
      PowerSeries.coeff (R := ℚ) 2 gq - 1 := by
    simp only [PowerSeries.coeff_mk, gammaCoeff_one, gammaCoeff_two, hgq1] at hγ2
    linarith
  rw [hB, hC, map_sub]
  change PowerSeries.coeff (R := ℚ) 2
      (zagierGenerating *
        MvPowerSeries.subst (fun (_ : Unit) => gq) (PowerSeries.mk betaCoeff)) -
      PowerSeries.coeff (R := ℚ) 2
        (zagierGenerating *
          MvPowerSeries.subst (fun (_ : Unit) => gq) (PowerSeries.mk gammaCoeff)) = _
  rw [coeff_mul_two, coeff_mul_two]
  simp only [zagierGenerating, generatingSeries, PowerSeries.coeff_mk,
    zagierC_zero, zagierC_one, zagierC_two, hβ0, hγ0, hβ1, hγ1,
    hβ2', hγ2', sub_zero]
  ring

theorem lcmSqIntegral_hA : LcmSqIntegral hA := lcmSqIntegral_zagierGenerating

theorem lcmSqIntegral_hB : LcmSqIntegral hB := by
  simpa only [hB, map_zagierIntegerGenerating] using
    lcmSqIntegral_mul_beta_subst zagierIntegerGenerating hauptmodulInverse
      constantCoeff_hauptmodulInverse

theorem lcmSqIntegral_hC : LcmSqIntegral hC := by
  simpa only [hC, map_zagierIntegerGenerating] using
    lcmSqIntegral_mul_gamma_subst zagierIntegerGenerating hauptmodulInverse
      constantCoeff_hauptmodulInverse

theorem h_combination_zero_iff (a b c : ℚ) :
    a • hA + b • hB + c • hC = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    have h0 := congrArg (PowerSeries.coeff (R := ℚ) 0) h
    have h1 := congrArg (PowerSeries.coeff (R := ℚ) 1) h
    have h2 := congrArg (PowerSeries.coeff (R := ℚ) 2) h
    have hB0 : PowerSeries.coeff (R := ℚ) 0 hB = 0 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hB_constantCoeff]
    have hC0 : PowerSeries.coeff (R := ℚ) 0 hC = 0 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hC_constantCoeff]
    have ha : a = 0 := by
      simpa only [map_add, map_smul, hA_coeff_zero, hB0, hC0,
        smul_eq_mul, mul_one, mul_zero, add_zero, map_zero] using h0
    subst a
    have hbc : b + c = 0 := by
      simpa only [zero_smul, zero_add, map_add, map_smul, hB_coeff_one,
        hC_coeff_one, smul_eq_mul, mul_one, map_zero] using h1
    have h2' : b * PowerSeries.coeff (R := ℚ) 2 hB +
        c * PowerSeries.coeff (R := ℚ) 2 hC = 0 := by
      simpa only [zero_smul, zero_add, map_add, map_smul,
        smul_eq_mul, map_zero, zero_mul, add_zero] using h2
    have hc : c = -b := by linarith
    have hdiff : PowerSeries.coeff (R := ℚ) 2 hB - PowerSeries.coeff (R := ℚ) 2 hC =
        -(1 / 4 : ℚ) := by
      simpa only [map_sub] using hB_sub_hC_coeff_two
    have hbprod : b * (PowerSeries.coeff (R := ℚ) 2 hB - PowerSeries.coeff (R := ℚ) 2 hC) = 0 := by
      rw [hc] at h2'
      nlinarith [h2']
    rw [hdiff] at hbprod
    have hb : b = 0 := by linarith
    exact ⟨rfl, hb, by simpa [hb] using hc⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp

theorem h_integer_combination_ne_zero {a b c : ℤ}
    (hnz : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    (a : ℚ) • hA + (b : ℚ) • hB + (c : ℚ) • hC ≠ 0 := by
  intro hzero
  have hcoeff := (h_combination_zero_iff (a : ℚ) (b : ℚ) (c : ℚ)).mp hzero
  rcases hnz with haz | hbz | hcz
  · exact haz (by exact_mod_cast hcoeff.1)
  · exact hbz (by exact_mod_cast hcoeff.2.1)
  · exact hcz (by exact_mod_cast hcoeff.2.2)

theorem lcmSqIntegral_h_integer_combination (a b c : ℤ) :
    LcmSqIntegral ((a : ℚ) • hA + (b : ℚ) • hB + (c : ℚ) • hC) := by
  intro n
  simp only [map_add, map_smul, smul_eq_mul]
  have ha := (lcmSqIntegral_hA n).mul_intCast a
  have hb := (lcmSqIntegral_hB n).mul_intCast b
  have hc := (lcmSqIntegral_hC n).mul_intCast c
  simpa only [mul_comm] using (ha.add hb).add hc

theorem hA_ode : generatingODE hA = 0 := by
  simpa only [hA] using zagierGenerating_ode

/-- The integer power series `x/(x-1) = -x/(1-x)`. -/
noncomputable def mobiusInvolution : PowerSeries ℤ :=
  -(PowerSeries.X * oneSubInv 1)

theorem constantCoeff_mobiusInvolution :
    PowerSeries.constantCoeff (R := ℤ) mobiusInvolution = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, mobiusInvolution,
    map_neg, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero]
  simp

set_option maxHeartbeats 800000 in
/-- The formal Mobius coordinate is an involution under substitution. -/
theorem mobiusInvolution_subst_self :
    MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolution) mobiusInvolution =
      PowerSeries.X := by
  let w : PowerSeries ℤ := mobiusInvolution
  let u : PowerSeries ℤ := oneSubInv 1
  have hw0 : PowerSeries.constantCoeff (R := ℤ) w = 0 := by
    exact constantCoeff_mobiusInvolution
  have hw : MvPowerSeries.HasSubst (fun (_ : Unit) => w) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hw0)
  have hsub_one : MvPowerSeries.subst (fun (_ : Unit) => w) (1 : PowerSeries ℤ) = 1 := by
    rw [← MvPowerSeries.substAlgHom_apply hw]
    exact map_one _
  have hsub_X : MvPowerSeries.subst (fun (_ : Unit) => w)
      (PowerSeries.X : PowerSeries ℤ) = w := by
    exact MvPowerSeries.subst_X hw ()
  have hwu : MvPowerSeries.subst (fun (_ : Unit) => w) u =
      1 - (PowerSeries.X : PowerSeries ℤ) := by
    have hinv : MvPowerSeries.subst (fun (_ : Unit) => w)
          (1 - (PowerSeries.X : PowerSeries ℤ)) *
        MvPowerSeries.subst (fun (_ : Unit) => w) u = 1 := by
      rw [← MvPowerSeries.subst_mul hw]
      rw [show (1 - (PowerSeries.X : PowerSeries ℤ)) * u =
          (1 - (PowerSeries.X : PowerSeries ℤ) ^ 1) * oneSubInv 1 by
            simp [u]]
      rw [oneSubInv_rightInv (k := 1) (by norm_num), hsub_one]
    have hsub_one_sub : MvPowerSeries.subst (fun (_ : Unit) => w)
          (1 - (PowerSeries.X : PowerSeries ℤ)) =
        1 - w := by
      calc
        MvPowerSeries.subst (fun (_ : Unit) => w)
              (1 - (PowerSeries.X : PowerSeries ℤ)) =
            MvPowerSeries.subst (fun (_ : Unit) => w) 1 -
              MvPowerSeries.subst (fun (_ : Unit) => w) PowerSeries.X := by
                rw [← MvPowerSeries.coe_substAlgHom hw]
                exact (MvPowerSeries.substAlgHom (σ := Unit) (τ := Unit)
                  (R := ℤ) (S := ℤ) hw).map_sub _ _
        _ = 1 - w := by
          calc
            _ = 1 - MvPowerSeries.subst (fun (_ : Unit) => w) PowerSeries.X :=
              congrArg (fun t => t - MvPowerSeries.subst
                (fun (_ : Unit) => w) PowerSeries.X) hsub_one
            _ = 1 - w := congrArg (fun t => 1 - t) hsub_X
    rw [hsub_one_sub] at hinv
    have hrel : 1 - w = u := by
      dsimp [w, mobiusInvolution, u]
      have hu : (1 - PowerSeries.X) * oneSubInv 1 = 1 := by
        simpa only [pow_one] using
          (oneSubInv_rightInv (k := 1) (by norm_num))
      calc
        1 - (-(PowerSeries.X * oneSubInv 1)) =
            1 + PowerSeries.X * oneSubInv 1 := by ring
        _ = (1 - PowerSeries.X) * oneSubInv 1 +
            PowerSeries.X * oneSubInv 1 := by rw [hu]
        _ = oneSubInv 1 := by ring
    rw [hrel] at hinv
    have hu_ne : u ≠ 0 := by
      intro hzero
      have hleft : u * (1 - PowerSeries.X) = 1 := by
        simpa [u, mul_comm, pow_one] using
          (oneSubInv_leftInv (k := 1) (by norm_num))
      rw [hzero, zero_mul] at hleft
      norm_num at hleft
    apply (mul_left_cancel₀ hu_ne)
    calc
      u * MvPowerSeries.subst (fun (_ : Unit) => w) u = 1 := hinv
      _ = u * (1 - PowerSeries.X) :=
        by simpa only [pow_one] using
          (oneSubInv_leftInv (k := 1) (by norm_num)).symm
  have hww : MvPowerSeries.subst (fun (_ : Unit) => w) w =
      -(w * MvPowerSeries.subst (fun (_ : Unit) => w) u) := by
    have hwdef : w = -(PowerSeries.X * u) := by rfl
    calc
      MvPowerSeries.subst (fun (_ : Unit) => w) w =
          MvPowerSeries.subst (fun (_ : Unit) => w) (-(PowerSeries.X * u)) :=
        congrArg (MvPowerSeries.subst (fun (_ : Unit) => w)) hwdef
      _ = -(w * MvPowerSeries.subst (fun (_ : Unit) => w) u) := by
        rw [← MvPowerSeries.substAlgHom_apply hw]
        simp only [map_neg, map_mul, MvPowerSeries.substAlgHom_X]
        have hXalg : (MvPowerSeries.substAlgHom hw)
            (PowerSeries.X : PowerSeries ℤ) = w := by
          change (MvPowerSeries.substAlgHom hw) (MvPowerSeries.X ()) = w
          exact MvPowerSeries.substAlgHom_X hw ()
        rw [hXalg, MvPowerSeries.substAlgHom_apply]
  rw [hww, hwu]
  rw [show w = -(PowerSeries.X * u) by rfl]
  rw [show -( -(PowerSeries.X * u) * (1 - PowerSeries.X)) =
      PowerSeries.X * (u * (1 - PowerSeries.X)) by ring]
  rw [show u * (1 - PowerSeries.X) = 1 by
    simpa [u, pow_one, mul_comm] using
      (oneSubInv_leftInv (k := 1) (by norm_num)), mul_one]

/-- The formal sum `f(x) + f(x/(x-1))` using the integer Möbius series. -/
noncomputable def symmetrizedFormal (f : PowerSeries ℚ) : PowerSeries ℚ :=
  f + MvPowerSeries.subst
    (fun (_ : Unit) => PowerSeries.map (Int.castRingHom ℚ) mobiusInvolution) f

theorem lcmSqIntegral_symmetrizedFormal {f : PowerSeries ℚ}
    (hf : LcmSqIntegral f) : LcmSqIntegral (symmetrizedFormal f) := by
  have hs := hf.subst_map_int mobiusInvolution constantCoeff_mobiusInvolution
  simpa only [symmetrizedFormal] using hf.add hs

end DirichletL

import Arithmetic.PowerSeriesInverse
import Arithmetic.ZagierSequences
import Analysis.GeneratingFunctions

/-!
Formal q-series part of CDT v2 Section 11.1, the Hauptmodul product before
equation `invert` (supplied `L2chi.tex` lines 7619-7637). Analytic modular
uniformization is not asserted here.
-/

namespace DirichletL

variable {R : Type*} [CommRing R]

/-- The degree-n coefficient of the finite product through factor n. -/
noncomputable def formalProductCoeff (f : ℕ → PowerSeries R) (n : ℕ) : R :=
  PowerSeries.coeff (R := R) n (∏ i ∈ Finset.range (n + 1), f i)

/-- The coefficient-stabilized formal infinite product. -/
noncomputable def formalProduct (f : ℕ → PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (formalProductCoeff f)

theorem coeff_formalProduct (f : ℕ → PowerSeries R) (n : ℕ) :
    PowerSeries.coeff (R := R) n (formalProduct f) = formalProductCoeff f n := by
  rw [formalProduct, PowerSeries.coeff_mk]

/-- A factor beginning in degree i+1 is invisible through degree i. -/
theorem coeff_eq_one_of_dvd_sub {f : PowerSeries R} {i n : ℕ}
    (h : PowerSeries.X ^ (i + 1) ∣ f - 1) (hn : n ≤ i) :
    PowerSeries.coeff (R := R) n f = if n = 0 then 1 else 0 := by
  have hz : PowerSeries.coeff (R := R) n (f - 1) = 0 := by
    apply PowerSeries.X_pow_dvd_iff.mp h
    omega
  rw [map_sub, sub_eq_zero] at hz
  simpa [PowerSeries.coeff_one, if_neg (by omega : ¬n + 1 = 0)] using hz

theorem coeff_formalProduct_stable {f : ℕ → PowerSeries R}
    (hf : ∀ i : ℕ, PowerSeries.X ^ (i + 1) ∣ f i - 1) {n N : ℕ} (hnN : n ≤ N) :
    PowerSeries.coeff (R := R) n (∏ i ∈ Finset.range (N + 1), f i) =
      formalProductCoeff f n := by
  rw [formalProductCoeff]
  induction N, hnN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    rw [Finset.range_succ, Finset.prod_insert]
    · rw [PowerSeries.coeff_mul]
      have hfac (j : ℕ) (hj : j ≤ n) :
          PowerSeries.coeff (R := R) j (f (N + 1)) = if j = 0 then 1 else 0 := by
        exact coeff_eq_one_of_dvd_sub (hf (N + 1))
          ((hj.trans hN).trans (Nat.le_succ N))
      rw [Finset.sum_eq_single (0, n)]
      · simpa [hfac 0 (by omega)] using ih
      · intro p hp hpne
        have hp1ne : p.1 ≠ 0 := by
          intro hp10
          apply hpne
          apply Prod.ext
          · exact hp10
          · have hsum := Finset.mem_antidiagonal.mp hp
            omega
        have hp1le : p.1 ≤ n := Finset.antidiagonal.fst_le hp
        simp [hfac p.1 hp1le, hp1ne]
      · intro hnot
        exact (hnot (by simp)).elim
    · simp [Finset.mem_range]

theorem dvd_pow_sub_one_of_dvd_sub_one {a d : PowerSeries R} (h : d ∣ a - 1) (e : ℕ) :
    d ∣ a ^ e - 1 := by
  exact dvd_trans h (by simpa using sub_dvd_pow_sub_pow a 1 e)

theorem dvd_X_pow_sub_one_sub {d k : ℕ} (hdk : d ≤ k) :
    (PowerSeries.X : PowerSeries R) ^ d ∣
      (1 - (PowerSeries.X : PowerSeries R) ^ k) - 1 := by
  have hp : (PowerSeries.X : PowerSeries R) ^ d ∣
      (PowerSeries.X : PowerSeries R) ^ k := pow_dvd_pow PowerSeries.X hdk
  obtain ⟨u, hu⟩ := hp
  refine ⟨-u, ?_⟩
  rw [hu]
  ring

/-- Exact inverse of `1-X^k` over the integer power-series ring. -/
noncomputable def oneSubInv (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.invOfUnit (1 - PowerSeries.X ^ k) (1 : Units ℤ)

theorem oneSubInv_rightInv {k : ℕ} (hk : 0 < k) :
    (1 - PowerSeries.X ^ k) * oneSubInv k = 1 := by
  apply PowerSeries.mul_invOfUnit
  simp [oneSubInv, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_X_pow, Nat.ne_of_gt hk]

theorem oneSubInv_leftInv {k : ℕ} (hk : 0 < k) :
    oneSubInv k * (1 - PowerSeries.X ^ k) = 1 := by
  rw [mul_comm]
  exact oneSubInv_rightInv hk

theorem constantCoeff_oneSubInv (k : ℕ) :
    PowerSeries.constantCoeff (R := ℤ) (oneSubInv k) = 1 := by
  simp [oneSubInv]

theorem coeff_oneSubInv_of_lt {k n : ℕ} (hnk : n < k) :
    PowerSeries.coeff (R := ℤ) n (oneSubInv k) = if n = 0 then 1 else 0 := by
  have hmul := congrArg (PowerSeries.coeff (R := ℤ) n) (oneSubInv_rightInv (by omega : 0 < k))
  rw [PowerSeries.coeff_mul] at hmul
  have hfac (j : ℕ) (hj : j ≤ n) :
      PowerSeries.coeff (R := ℤ) j (1 - PowerSeries.X ^ k) = if j = 0 then 1 else 0 := by
    rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
    have hjk : j ≠ k := by
      exact ne_of_lt (lt_of_le_of_lt hj hnk)
    simp [hjk]
  calc
    PowerSeries.coeff (R := ℤ) n (oneSubInv k) =
        ∑ p ∈ (Finset.antidiagonal n : Finset (ℕ × ℕ)),
          PowerSeries.coeff (R := ℤ) p.1 (1 - PowerSeries.X ^ k) *
            PowerSeries.coeff (R := ℤ) p.2 (oneSubInv k) := by
          rw [Finset.sum_eq_single (0, n)]
          · simp [hfac 0 (by omega)]
          · intro p hp hpne
            have hp1ne : p.1 ≠ 0 := by
              intro hp10
              apply hpne
              apply Prod.ext
              · exact hp10
              · have hsum := Finset.mem_antidiagonal.mp hp
                omega
            have hp1le : p.1 ≤ n := Finset.antidiagonal.fst_le hp
            simp [hfac p.1 hp1le, hp1ne]
          · exact by simp
    _ = PowerSeries.coeff (R := ℤ) n 1 := hmul
    _ = if n = 0 then 1 else 0 := by simp [PowerSeries.coeff_one]

theorem dvd_oneSubInv_sub_one {k d : ℕ} (hk : 0 < k) (hdk : d ≤ k) :
    PowerSeries.X ^ d ∣ oneSubInv k - 1 := by
  have heq : oneSubInv k - 1 = PowerSeries.X ^ k * oneSubInv k := by
    calc
      oneSubInv k - 1 = oneSubInv k -
          (1 - PowerSeries.X ^ k) * oneSubInv k := by rw [oneSubInv_rightInv hk]
      _ = PowerSeries.X ^ k * oneSubInv k := by ring
  obtain ⟨u, hu⟩ := pow_dvd_pow (PowerSeries.X : PowerSeries ℤ) hdk
  refine ⟨u * oneSubInv k, ?_⟩
  rw [heq, hu]
  ring

/-- The positive-index factor in the Hauptmodul product. -/
noncomputable def hauptFactor (i : ℕ) : PowerSeries ℤ :=
  (1 - PowerSeries.X ^ (i + 1)) ^ 4 *
    (1 - PowerSeries.X ^ (6 * (i + 1))) ^ 8 *
    oneSubInv (2 * (i + 1)) ^ 8 *
    oneSubInv (3 * (i + 1)) ^ 4

theorem dvd_hauptFactor_sub_one (i : ℕ) :
    PowerSeries.X ^ (i + 1) ∣ hauptFactor i - 1 := by
  let d := i + 1
  have hnum : (PowerSeries.X : PowerSeries ℤ) ^ d ∣
      (1 - PowerSeries.X ^ d) ^ 4 - 1 :=
    dvd_pow_sub_one_of_dvd_sub_one (dvd_X_pow_sub_one_sub (le_rfl)) 4
  have hnum6 : (PowerSeries.X : PowerSeries ℤ) ^ d ∣
      (1 - PowerSeries.X ^ (6 * d)) ^ 8 - 1 :=
    dvd_pow_sub_one_of_dvd_sub_one (dvd_X_pow_sub_one_sub (by omega)) 8
  have hinv2 : (PowerSeries.X : PowerSeries ℤ) ^ d ∣ oneSubInv (2 * d) ^ 8 - 1 :=
    dvd_pow_sub_one_of_dvd_sub_one
      (dvd_oneSubInv_sub_one (by omega) (by omega)) 8
  have hinv3 : (PowerSeries.X : PowerSeries ℤ) ^ d ∣ oneSubInv (3 * d) ^ 4 - 1 :=
    dvd_pow_sub_one_of_dvd_sub_one
      (dvd_oneSubInv_sub_one (by omega) (by omega)) 4
  have hmul {a b : PowerSeries ℤ}
      (ha : (PowerSeries.X : PowerSeries ℤ) ^ d ∣ a - 1)
      (hb : (PowerSeries.X : PowerSeries ℤ) ^ d ∣ b - 1) :
      (PowerSeries.X : PowerSeries ℤ) ^ d ∣ a * b - 1 := by
    obtain ⟨u, hu⟩ := ha
    obtain ⟨v, hv⟩ := hb
    have ha' : a = 1 + (PowerSeries.X : PowerSeries ℤ) ^ d * u := by
      calc
        a = (a - 1) + 1 := by ring
        _ = (PowerSeries.X : PowerSeries ℤ) ^ d * u + 1 := by rw [hu]
        _ = _ := by ring
    have hb' : b = 1 + (PowerSeries.X : PowerSeries ℤ) ^ d * v := by
      calc
        b = (b - 1) + 1 := by ring
        _ = (PowerSeries.X : PowerSeries ℤ) ^ d * v + 1 := by rw [hv]
        _ = _ := by ring
    refine ⟨a * v + u, ?_⟩
    rw [ha', hb']
    ring
  unfold hauptFactor
  exact hmul (hmul (hmul hnum hnum6) hinv2) hinv3

theorem constantCoeff_hauptFactor (i : ℕ) :
    PowerSeries.constantCoeff (R := ℤ) (hauptFactor i) = 1 := by
  have hsub (k : ℕ) (hk : k ≠ 0) :
      PowerSeries.constantCoeff (R := ℤ) (1 - PowerSeries.X ^ k) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [PowerSeries.coeff_X_pow, hk]
  simp [hauptFactor, hsub, constantCoeff_oneSubInv]

theorem constantCoeff_formalProduct_hauptFactor :
    PowerSeries.constantCoeff (R := ℤ) (formalProduct hauptFactor) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_formalProduct,
    formalProductCoeff]
  simp [constantCoeff_hauptFactor]

theorem coeff_formalProduct_hauptFactor_stable {n N : ℕ} (hnN : n ≤ N) :
    PowerSeries.coeff (R := ℤ) n (∏ i ∈ Finset.range (N + 1), hauptFactor i) =
      formalProductCoeff hauptFactor n :=
  coeff_formalProduct_stable dvd_hauptFactor_sub_one hnN

/-- The formal q-series corresponding to CDT's Hauptmodul product. -/
noncomputable def hauptmodul : PowerSeries ℤ :=
  PowerSeries.X * formalProduct hauptFactor

theorem constantCoeff_hauptmodul :
    PowerSeries.constantCoeff (R := ℤ) hauptmodul = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hauptmodul,
    PowerSeries.coeff_mul]
  simp

theorem coeff_one_hauptmodul :
    PowerSeries.coeff (R := ℤ) 1 hauptmodul = 1 := by
  rw [hauptmodul, PowerSeries.coeff_mul]
  rw [Finset.Nat.antidiagonal_succ 0]
  simp [coeff_formalProduct, formalProductCoeff, hauptFactor,
    oneSubInv_rightInv, constantCoeff_oneSubInv]

private theorem haupt_coeff_two_mul (f g : PowerSeries ℤ) :
    PowerSeries.coeff (R := ℤ) 2 (f * g) =
      PowerSeries.coeff (R := ℤ) 0 f * PowerSeries.coeff (R := ℤ) 2 g +
        PowerSeries.coeff (R := ℤ) 1 f * PowerSeries.coeff (R := ℤ) 1 g +
          PowerSeries.coeff (R := ℤ) 2 f * PowerSeries.coeff (R := ℤ) 0 g := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_eq_map, Finset.sum_map]
  norm_num [Finset.sum_range_succ]

private theorem haupt_coeff_two_oneSubInv_two :
    PowerSeries.coeff (R := ℤ) 2 (oneSubInv 2) = 1 := by
  have h := congrArg (PowerSeries.coeff (R := ℤ) 2)
    (oneSubInv_rightInv (k := 2) (by norm_num))
  rw [haupt_coeff_two_mul] at h
  unfold oneSubInv at h ⊢
  simp [PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
  linarith

private theorem haupt_coeff_one_factor_zero :
    PowerSeries.coeff (R := ℤ) 1 (hauptFactor 0) = -4 := by
  simp [hauptFactor, PowerSeries.coeff_one_mul, PowerSeries.coeff_one_pow,
    coeff_oneSubInv_of_lt, constantCoeff_oneSubInv]

private theorem haupt_coeff_one_factor_one :
    PowerSeries.coeff (R := ℤ) 1 (hauptFactor 1) = 0 := by
  simp [hauptFactor, PowerSeries.coeff_one_mul, PowerSeries.coeff_one_pow,
    coeff_oneSubInv_of_lt, constantCoeff_oneSubInv]

private theorem haupt_coeff_two_factor_zero :
    PowerSeries.coeff (R := ℤ) 2 (hauptFactor 0) = 14 := by
  simp [hauptFactor, haupt_coeff_two_mul, PowerSeries.coeff_one_mul, pow_succ,
    PowerSeries.coeff_one_pow, PowerSeries.coeff_X,
    coeff_oneSubInv_of_lt, constantCoeff_oneSubInv,
    haupt_coeff_two_oneSubInv_two]

private theorem haupt_coeff_two_factor_one :
    PowerSeries.coeff (R := ℤ) 2 (hauptFactor 1) = -4 := by
  simp [hauptFactor, haupt_coeff_two_mul, PowerSeries.coeff_one_mul, pow_succ,
    PowerSeries.coeff_one_pow, PowerSeries.coeff_X,
    coeff_oneSubInv_of_lt, constantCoeff_oneSubInv,
    haupt_coeff_two_oneSubInv_two]

private theorem haupt_coeff_one_factor_two :
    PowerSeries.coeff (R := ℤ) 1 (hauptFactor 2) = 0 := by
  simp [hauptFactor, PowerSeries.coeff_one_mul, PowerSeries.coeff_one_pow,
    coeff_oneSubInv_of_lt, constantCoeff_oneSubInv]

private theorem haupt_coeff_two_factor_two :
    PowerSeries.coeff (R := ℤ) 2 (hauptFactor 2) = 0 := by
  simp [hauptFactor, haupt_coeff_two_mul, PowerSeries.coeff_one_mul, pow_succ,
    PowerSeries.coeff_one_pow, PowerSeries.coeff_X,
    coeff_oneSubInv_of_lt, constantCoeff_oneSubInv,
    haupt_coeff_two_oneSubInv_two]

private theorem haupt_coeff_one_formalProduct :
    PowerSeries.coeff (R := ℤ) 1 (formalProduct hauptFactor) = -4 := by
  rw [coeff_formalProduct]
  unfold formalProductCoeff
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  rw [PowerSeries.coeff_one_mul]
  rw [haupt_coeff_one_factor_zero, haupt_coeff_one_factor_one,
    constantCoeff_hauptFactor, constantCoeff_hauptFactor]
  norm_num

private theorem haupt_coeff_two_formalProduct :
    PowerSeries.coeff (R := ℤ) 2 (formalProduct hauptFactor) = 10 := by
  rw [coeff_formalProduct]
  unfold formalProductCoeff
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  rw [haupt_coeff_two_mul]
  have hp0 : PowerSeries.coeff (R := ℤ) 0 (hauptFactor 0 * hauptFactor 1) = 1 := by
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_hauptFactor]
  have hp1 : PowerSeries.coeff (R := ℤ) 1 (hauptFactor 0 * hauptFactor 1) = -4 := by
    rw [PowerSeries.coeff_one_mul]
    rw [haupt_coeff_one_factor_zero, haupt_coeff_one_factor_one,
      constantCoeff_hauptFactor, constantCoeff_hauptFactor]
    norm_num
  have hp2 : PowerSeries.coeff (R := ℤ) 2 (hauptFactor 0 * hauptFactor 1) = 10 := by
    rw [haupt_coeff_two_mul]
    rw [haupt_coeff_one_factor_zero, haupt_coeff_one_factor_one,
      haupt_coeff_two_factor_zero, haupt_coeff_two_factor_one,
      PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_zero_eq_constantCoeff_apply,
      constantCoeff_hauptFactor, constantCoeff_hauptFactor]
    norm_num
  rw [hp0, hp1, hp2, haupt_coeff_two_factor_two, haupt_coeff_one_factor_two,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_hauptFactor]
  norm_num

/-- The degree-two coefficient in CDT v2 Section 11.1, equation `haupt`.
This is the first displayed coefficient after the leading `q` term. -/
theorem coeff_two_hauptmodul : PowerSeries.coeff (R := ℤ) 2 hauptmodul = -4 := by
  rw [hauptmodul, PowerSeries.coeff_succ_X_mul, haupt_coeff_one_formalProduct]

/-- The degree-three coefficient in CDT v2 Section 11.1, equation `haupt`. -/
theorem coeff_three_hauptmodul : PowerSeries.coeff (R := ℤ) 3 hauptmodul = 10 := by
  rw [hauptmodul, PowerSeries.coeff_succ_X_mul, haupt_coeff_two_formalProduct]

theorem exists_hauptmodul_subst_inverse :
    ∃ g : PowerSeries ℤ, PowerSeries.constantCoeff (R := ℤ) g = 0 ∧
      PowerSeries.coeff (R := ℤ) 1 g = 1 ∧
      MvPowerSeries.subst (fun (_ : Unit) => hauptmodul) g = PowerSeries.X ∧
      MvPowerSeries.subst (fun (_ : Unit) => g) hauptmodul = PowerSeries.X := by
  exact exists_integral_subst_inverse hauptmodul constantCoeff_hauptmodul coeff_one_hauptmodul

/-- The integer-coefficient lift of the Zagier generating series. -/
noncomputable def zagierIntegerGenerating : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (zagierC n : ℤ))

theorem map_zagierIntegerGenerating :
    PowerSeries.map (Int.castRingHom ℚ) zagierIntegerGenerating = zagierGenerating := by
  ext n
  simp [zagierIntegerGenerating, zagierGenerating, generatingSeries]

theorem lcmSqIntegral_zagierGenerating : LcmSqIntegral zagierGenerating := by
  intro n
  rw [zagierGenerating, generatingSeries, PowerSeries.coeff_mk]
  refine ⟨(lcmPrefix n : ℤ) ^ 2 * (zagierC n : ℤ), ?_⟩
  push_cast
  ring

theorem exists_lcmSqIntegral_hauptmodul_beta :
    ∃ g : PowerSeries ℤ,
      PowerSeries.constantCoeff (R := ℤ) g = 0 ∧
      PowerSeries.coeff (R := ℤ) 1 g = 1 ∧
      MvPowerSeries.subst (fun (_ : Unit) => hauptmodul) g = PowerSeries.X ∧
      MvPowerSeries.subst (fun (_ : Unit) => g) hauptmodul = PowerSeries.X ∧
      LcmSqIntegral
        (zagierGenerating *
          MvPowerSeries.subst (fun (_ : Unit) => PowerSeries.map (Int.castRingHom ℚ) g)
            (PowerSeries.mk betaCoeff)) := by
  obtain ⟨g, hg0, hg1, hgf, hfg⟩ := exists_hauptmodul_subst_inverse
  refine ⟨g, hg0, hg1, hgf, hfg, ?_⟩
  simpa only [map_zagierIntegerGenerating] using
    lcmSqIntegral_mul_beta_subst zagierIntegerGenerating g hg0

theorem exists_lcmSqIntegral_hauptmodul_gamma :
    ∃ g : PowerSeries ℤ,
      PowerSeries.constantCoeff (R := ℤ) g = 0 ∧
      PowerSeries.coeff (R := ℤ) 1 g = 1 ∧
      MvPowerSeries.subst (fun (_ : Unit) => hauptmodul) g = PowerSeries.X ∧
      MvPowerSeries.subst (fun (_ : Unit) => g) hauptmodul = PowerSeries.X ∧
      LcmSqIntegral
        (zagierGenerating *
          MvPowerSeries.subst (fun (_ : Unit) => PowerSeries.map (Int.castRingHom ℚ) g)
            (PowerSeries.mk gammaCoeff)) := by
  obtain ⟨g, hg0, hg1, hgf, hfg⟩ := exists_hauptmodul_subst_inverse
  refine ⟨g, hg0, hg1, hgf, hfg, ?_⟩
  simpa only [map_zagierIntegerGenerating] using
    lcmSqIntegral_mul_gamma_subst zagierIntegerGenerating g hg0

end DirichletL

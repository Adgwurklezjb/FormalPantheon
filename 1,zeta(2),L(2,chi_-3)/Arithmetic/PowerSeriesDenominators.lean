import Arithmetic.Denominators

/-!
Squared prefix-lcm denominator transfer for formal products and substitutions.
This is the algebraic step in CDT v2, Section 11.1, equation `invert` and
Lemma `defabc` (supplied `L2chi.tex` lines 7633-7640 and 7688-7711).
-/

namespace DirichletL

/-- Substitution by a zero-constant series has a finite coefficient formula. -/
theorem coeff_subst_eq_sum {R : Type*} [CommRing R] (f g : PowerSeries R)
    (hg : PowerSeries.constantCoeff (R := R) g = 0) (n : ℕ) :
    PowerSeries.coeff (R := R) n (MvPowerSeries.subst (fun (_ : Unit) => g) f) =
      ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff (R := R) k f *
        PowerSeries.coeff (R := R) n (g ^ k) := by
  have hs : MvPowerSeries.HasSubst (fun (_ : Unit) => g) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hg)
  have hbij : Function.Bijective (Finsupp.single () : ℕ → Unit →₀ ℕ) := by
    refine ⟨Finsupp.single_injective (), ?_⟩
    intro d
    exact ⟨d (), by ext; simp⟩
  change MvPowerSeries.coeff (R := R) (Finsupp.single () n) _ = _
  rw [MvPowerSeries.coeff_subst hs, ← finsum_comp _ hbij]
  have hprod (k : ℕ) :
      (Finsupp.single () k).prod (fun (_ : Unit) e => g ^ e) = g ^ k :=
    Finsupp.prod_single_index (pow_zero g)
  simp only [hprod, smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  by_contra hkn
  have hnk : n < k := by simpa using hkn
  have hz : PowerSeries.coeff (R := R) n (g ^ k) = 0 :=
    PowerSeries.X_pow_dvd_iff.mp
      (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr hg) k) n hnk
  apply hk
  change PowerSeries.coeff (R := R) k f * PowerSeries.coeff (R := R) n (g ^ k) = 0
  rw [hz, mul_zero]

/-- Every coefficient is cleared by the squared lcm of its positive prefix. -/
def LcmSqIntegral (f : PowerSeries ℚ) : Prop :=
  ∀ n : ℕ, SqIntegral (PowerSeries.coeff (R := ℚ) n f) (lcmPrefix n)

theorem LcmSqIntegral.add {f g : PowerSeries ℚ} (hf : LcmSqIntegral f)
    (hg : LcmSqIntegral g) : LcmSqIntegral (f + g) := by
  intro n
  rw [map_add]
  exact (hf n).add (hg n)

/-- An integer series can multiply a series without enlarging its lcm bound. -/
theorem LcmSqIntegral.mul_map_int {f : PowerSeries ℚ} (hf : LcmSqIntegral f)
    (g : PowerSeries ℤ) :
    LcmSqIntegral (f * PowerSeries.map (Int.castRingHom ℚ) g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  apply SqIntegral.sum
  intro p hp
  rw [PowerSeries.coeff_map]
  exact ((hf p.1).of_dvd (lcmPrefix_dvd (Finset.antidiagonal.fst_le hp))).mul_intCast
    (PowerSeries.coeff (R := ℤ) p.2 g)

/-- Integral substitution with zero constant coefficient preserves the lcm bound. -/
theorem LcmSqIntegral.subst_map_int {f : PowerSeries ℚ} (hf : LcmSqIntegral f)
    (g : PowerSeries ℤ) (hg : PowerSeries.constantCoeff (R := ℤ) g = 0) :
    LcmSqIntegral
      (MvPowerSeries.subst (fun (_ : Unit) => PowerSeries.map (Int.castRingHom ℚ) g) f) := by
  intro n
  have hgq : PowerSeries.constantCoeff (R := ℚ) (PowerSeries.map (Int.castRingHom ℚ) g) = 0 := by
    change (PowerSeries.constantCoeff (R := ℤ) g : ℚ) = 0
    rw [hg, Int.cast_zero]
  rw [coeff_subst_eq_sum f _ hgq]
  apply SqIntegral.sum
  intro k hk
  rw [← map_pow, PowerSeries.coeff_map]
  exact ((hf k).of_dvd (lcmPrefix_dvd (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))).mul_intCast
    (PowerSeries.coeff (R := ℤ) n (g ^ k))

theorem lcmSqIntegral_beta : LcmSqIntegral (PowerSeries.mk betaCoeff) := by
  intro n
  rw [PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · subst n
    rw [betaCoeff_zero]
    exact SqIntegral.zero _
  · exact sqIntegral_lcmPrefix hn (sqIntegral_betaCoeff hn)

theorem lcmSqIntegral_gamma : LcmSqIntegral (PowerSeries.mk gammaCoeff) := by
  intro n
  rw [PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · subst n
    simpa [gammaCoeff] using SqIntegral.zero (lcmPrefix 0)
  · exact sqIntegral_lcmPrefix hn (sqIntegral_gammaCoeff hn)

/-- The denominator conclusion for the formal product used to construct H_B. -/
theorem lcmSqIntegral_mul_beta_subst (a g : PowerSeries ℤ)
    (hg : PowerSeries.constantCoeff (R := ℤ) g = 0) :
    LcmSqIntegral (PowerSeries.map (Int.castRingHom ℚ) a *
      MvPowerSeries.subst (fun (_ : Unit) => PowerSeries.map (Int.castRingHom ℚ) g)
        (PowerSeries.mk betaCoeff)) := by
  rw [mul_comm]
  exact (lcmSqIntegral_beta.subst_map_int g hg).mul_map_int a

/-- The denominator conclusion for the formal product used to construct H_C. -/
theorem lcmSqIntegral_mul_gamma_subst (a g : PowerSeries ℤ)
    (hg : PowerSeries.constantCoeff (R := ℤ) g = 0) :
    LcmSqIntegral (PowerSeries.map (Int.castRingHom ℚ) a *
      MvPowerSeries.subst (fun (_ : Unit) => PowerSeries.map (Int.castRingHom ℚ) g)
        (PowerSeries.mk gammaCoeff)) := by
  rw [mul_comm]
  exact (lcmSqIntegral_gamma.subst_map_int g hg).mul_map_int a

end DirichletL

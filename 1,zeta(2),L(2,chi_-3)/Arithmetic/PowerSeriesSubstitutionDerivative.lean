import Arithmetic.PowerSeriesDenominators

/-!
Formal substitution chain rule for the Mobius change of variable in CDT v2,
Lemma `etalecover`, equation `y in x`, and equation `explicitode`.
The proof reduces each coefficient to Mathlib's polynomial chain rule.
-/

namespace DirichletL

variable {R : Type*} [CommRing R]

/-- A substituted coefficient depends only on the input coefficients up to its index. -/
theorem coeff_subst_congr (g : PowerSeries R) (hg : PowerSeries.constantCoeff (R := R) g = 0)
    {f p : PowerSeries R} (n : ℕ)
    (hfp : ∀ k : ℕ, k ≤ n → PowerSeries.coeff (R := R) k f = PowerSeries.coeff (R := R) k p) :
    PowerSeries.coeff (R := R) n (MvPowerSeries.subst (fun (_ : Unit) => g) f) =
      PowerSeries.coeff (R := R) n (MvPowerSeries.subst (fun (_ : Unit) => g) p) := by
  rw [coeff_subst_eq_sum f g hg, coeff_subst_eq_sum p g hg]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hfp k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]

/-- Substitution of a polynomial agrees with its canonical algebra evaluation. -/
theorem subst_coe_polynomial_eq_aeval (g : PowerSeries R)
    (hg : PowerSeries.constantCoeff (R := R) g = 0) (p : Polynomial R) :
    MvPowerSeries.subst (fun (_ : Unit) => g) (p : PowerSeries R) =
      Polynomial.aeval g p := by
  have hs : MvPowerSeries.HasSubst (fun (_ : Unit) => g) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hg)
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [MvPowerSeries.subst_add hs, hp, hq]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_pow, Polynomial.coe_X, MvPowerSeries.subst_mul hs,
      MvPowerSeries.subst_pow hs]
    have hX : MvPowerSeries.subst (fun (_ : Unit) => g) (PowerSeries.X : PowerSeries R) = g :=
      MvPowerSeries.subst_X hs ()
    have hC : MvPowerSeries.subst (fun (_ : Unit) => g) (PowerSeries.C (R := R) a) =
        PowerSeries.C (R := R) a := by
      rw [← MvPowerSeries.substAlgHom_apply hs]
      exact (MvPowerSeries.substAlgHom hs).commutes a
    simp [hC, hX]

/-- The formal chain rule, including substitution by a ramified coordinate. -/
theorem derivativeFun_subst (f g : PowerSeries R)
    (hg : PowerSeries.constantCoeff (R := R) g = 0) :
    PowerSeries.derivativeFun (MvPowerSeries.subst (fun (_ : Unit) => g) f) =
      MvPowerSeries.subst (fun (_ : Unit) => g) f.derivativeFun * g.derivativeFun := by
  ext n
  let p : Polynomial R := PowerSeries.trunc (n + 2) f
  have hp (k : ℕ) (hk : k ≤ n + 1) :
      PowerSeries.coeff (R := R) k (p : PowerSeries R) = PowerSeries.coeff (R := R) k f := by
    exact PowerSeries.coeff_coe_trunc_of_lt (by omega)
  have hpd (k : ℕ) (hk : k ≤ n) :
      PowerSeries.coeff (R := R) k (p.derivative : PowerSeries R) =
        PowerSeries.coeff (R := R) k f.derivativeFun := by
    rw [Polynomial.coeff_coe, Polynomial.coeff_derivative, PowerSeries.coeff_derivativeFun]
    rw [← Polynomial.coeff_coe, hp (k + 1) (by omega)]
  have hpoly :
      PowerSeries.derivativeFun
        (MvPowerSeries.subst (fun (_ : Unit) => g) (p : PowerSeries R)) =
        MvPowerSeries.subst (fun (_ : Unit) => g) (p.derivative : PowerSeries R) *
          g.derivativeFun := by
    rw [subst_coe_polynomial_eq_aeval g hg, subst_coe_polynomial_eq_aeval g hg]
    exact (PowerSeries.derivative R).map_aeval p g
  calc
    PowerSeries.coeff (R := R) n
        (PowerSeries.derivativeFun (MvPowerSeries.subst (fun (_ : Unit) => g) f)) =
        PowerSeries.coeff (R := R) n (PowerSeries.derivativeFun
          (MvPowerSeries.subst (fun (_ : Unit) => g) (p : PowerSeries R))) := by
      rw [PowerSeries.coeff_derivativeFun, PowerSeries.coeff_derivativeFun,
        coeff_subst_congr g hg (n + 1) (fun k hk => (hp k hk).symm)]
    _ = PowerSeries.coeff (R := R) n
        (MvPowerSeries.subst (fun (_ : Unit) => g) (p.derivative : PowerSeries R) *
          g.derivativeFun) := congrArg (PowerSeries.coeff (R := R) n) hpoly
    _ = _ := by
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro kl hkl
      rw [coeff_subst_congr g hg kl.1
        (fun k hk => hpd k (hk.trans (Finset.antidiagonal.fst_le hkl)))]

/-- The second formal chain rule, with ordinary derivatives. -/
theorem derivativeFun_subst_two (f g : PowerSeries R)
    (hg : PowerSeries.constantCoeff (R := R) g = 0) :
    PowerSeries.derivativeFun (PowerSeries.derivativeFun
        (MvPowerSeries.subst (fun (_ : Unit) => g) f)) =
      MvPowerSeries.subst (fun (_ : Unit) => g) f.derivativeFun.derivativeFun *
          g.derivativeFun ^ 2 +
        MvPowerSeries.subst (fun (_ : Unit) => g) f.derivativeFun *
          g.derivativeFun.derivativeFun := by
  rw [derivativeFun_subst f g hg, PowerSeries.derivativeFun_mul]
  simp only [derivativeFun_subst _ g hg, smul_eq_mul]
  ring

/-- The third formal chain rule, including ramified inner series. -/
theorem derivativeFun_subst_three (f g : PowerSeries R)
    (hg : PowerSeries.constantCoeff (R := R) g = 0) :
    PowerSeries.derivativeFun (PowerSeries.derivativeFun (PowerSeries.derivativeFun
        (MvPowerSeries.subst (fun (_ : Unit) => g) f))) =
      MvPowerSeries.subst (fun (_ : Unit) => g)
          f.derivativeFun.derivativeFun.derivativeFun * g.derivativeFun ^ 3 +
        3 * MvPowerSeries.subst (fun (_ : Unit) => g) f.derivativeFun.derivativeFun *
          g.derivativeFun * g.derivativeFun.derivativeFun +
        MvPowerSeries.subst (fun (_ : Unit) => g) f.derivativeFun *
          g.derivativeFun.derivativeFun.derivativeFun := by
  rw [derivativeFun_subst_two f g hg]
  have hpow : PowerSeries.derivativeFun (g.derivativeFun ^ 2) =
      2 * g.derivativeFun * g.derivativeFun.derivativeFun := by
    simpa only [smul_eq_mul, nsmul_eq_mul, Nat.reduceSub, Nat.cast_ofNat,
      pow_one, mul_assoc] using
      (PowerSeries.derivative R).leibniz_pow g.derivativeFun 2
  simp only [PowerSeries.derivativeFun_add, PowerSeries.derivativeFun_mul,
    derivativeFun_subst _ g hg, smul_eq_mul, hpow]
  ring

/-- The fourth formal chain rule used by CDT's descended operator. -/
theorem derivativeFun_subst_four (f g : PowerSeries R)
    (hg : PowerSeries.constantCoeff (R := R) g = 0) :
    PowerSeries.derivativeFun (PowerSeries.derivativeFun (PowerSeries.derivativeFun
        (PowerSeries.derivativeFun (MvPowerSeries.subst (fun (_ : Unit) => g) f)))) =
      MvPowerSeries.subst (fun (_ : Unit) => g)
          f.derivativeFun.derivativeFun.derivativeFun.derivativeFun * g.derivativeFun ^ 4 +
        6 * MvPowerSeries.subst (fun (_ : Unit) => g)
          f.derivativeFun.derivativeFun.derivativeFun * g.derivativeFun ^ 2 *
          g.derivativeFun.derivativeFun +
        MvPowerSeries.subst (fun (_ : Unit) => g) f.derivativeFun.derivativeFun *
          (3 * g.derivativeFun.derivativeFun ^ 2 +
            4 * g.derivativeFun * g.derivativeFun.derivativeFun.derivativeFun) +
        MvPowerSeries.subst (fun (_ : Unit) => g) f.derivativeFun *
          g.derivativeFun.derivativeFun.derivativeFun.derivativeFun := by
  rw [derivativeFun_subst_three f g hg]
  have hpow : PowerSeries.derivativeFun (g.derivativeFun ^ 3) =
      3 * g.derivativeFun ^ 2 * g.derivativeFun.derivativeFun := by
    simpa only [smul_eq_mul, nsmul_eq_mul, Nat.reduceSub, Nat.cast_ofNat,
      mul_assoc] using
      (PowerSeries.derivative R).leibniz_pow g.derivativeFun 3
  have h3 : PowerSeries.derivativeFun (3 : PowerSeries R) = 0 :=
    (PowerSeries.derivative R).map_natCast 3
  simp only [PowerSeries.derivativeFun_add, PowerSeries.derivativeFun_mul,
    derivativeFun_subst _ g hg, smul_eq_mul, hpow, h3, mul_zero, add_zero]
  ring

end DirichletL

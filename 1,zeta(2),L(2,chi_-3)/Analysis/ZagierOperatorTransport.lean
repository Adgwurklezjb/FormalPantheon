import Analysis.GeneratingFunctions
import Arithmetic.PowerSeriesEuler
import Arithmetic.PowerSeriesSubstitutionDerivative

/-!
Formal transport of the case-C operator through an Eichler-integral product.
This is the calculation following Zagier (2009), Section 5, equation (7),
with the additional factor used in CDT v2, Section 11.1, `functionsH`.
-/

namespace DirichletL

private theorem euler_subst (F H : PowerSeries ℚ)
    (hH0 : PowerSeries.constantCoeff (R := ℚ) H = 0) :
    powerSeriesEuler ℚ (MvPowerSeries.subst (fun (_ : Unit) => H) F) =
      MvPowerSeries.subst (fun (_ : Unit) => H) F.derivativeFun *
        powerSeriesEuler ℚ H := by
  simp only [powerSeriesEuler_apply, derivativeFun_subst F H hH0]
  ring

private theorem euler_subst_two (F H : PowerSeries ℚ)
    (hH0 : PowerSeries.constantCoeff (R := ℚ) H = 0) :
    powerSeriesEuler ℚ (powerSeriesEuler ℚ
      (MvPowerSeries.subst (fun (_ : Unit) => H) F)) =
      MvPowerSeries.subst (fun (_ : Unit) => H) F.derivativeFun.derivativeFun *
          (powerSeriesEuler ℚ H) ^ 2 +
        MvPowerSeries.subst (fun (_ : Unit) => H) F.derivativeFun *
          powerSeriesEuler ℚ (powerSeriesEuler ℚ H) := by
  rw [euler_subst F H hH0, Derivation.leibniz, euler_subst F.derivativeFun H hH0]
  simp only [smul_eq_mul]
  ring

private theorem euler_sq (f : PowerSeries ℚ) :
    powerSeriesEuler ℚ (f ^ 2) = 2 * f * powerSeriesEuler ℚ f := by
  simpa only [nsmul_eq_mul, smul_eq_mul, Nat.reduceSub, pow_one, Nat.cast_ofNat,
    mul_assoc] using (powerSeriesEuler ℚ).leibniz_pow f 2

/-- The case-C operator on F, pulled back through F(H)=f*V. -/
theorem subst_generatingODE_mul_of_euler_identities (f F H V : PowerSeries ℚ)
    (hH0 : PowerSeries.constantCoeff (R := ℚ) H = 0) (hfne : f ≠ 0)
    (hcomp : MvPowerSeries.subst (fun (_ : Unit) => H) F = f * V)
    (hH : powerSeriesEuler ℚ H = H * (1 - 10 * H + 9 * H ^ 2) * f ^ 2)
    (hf : 2 * (powerSeriesEuler ℚ f) ^ 2 -
        f * powerSeriesEuler ℚ (powerSeriesEuler ℚ f) =
      H * (1 - 10 * H + 9 * H ^ 2) * (9 * H - 3) * f ^ 6) :
    H * (1 - 10 * H + 9 * H ^ 2) * f ^ 3 *
        MvPowerSeries.subst (fun (_ : Unit) => H) (generatingODE F) =
      powerSeriesEuler ℚ (powerSeriesEuler ℚ V) := by
  let α : PowerSeries ℚ := H * (1 - 10 * H + 9 * H ^ 2)
  let α' : PowerSeries ℚ := 1 - 20 * H + 27 * H ^ 2
  have hs : MvPowerSeries.HasSubst (fun (_ : Unit) => H) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hH0)
  let S : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ := MvPowerSeries.substAlgHom hs
  have hS (p : PowerSeries ℚ) : S p = MvPowerSeries.subst (fun (_ : Unit) => H) p :=
    MvPowerSeries.substAlgHom_apply hs p
  have hSX : S PowerSeries.X = H := by
    rw [hS]
    exact MvPowerSeries.subst_X hs ()
  have hODE : S (generatingODE F) =
      α * S F.derivativeFun.derivativeFun + α' * S F.derivativeFun + (9 * H - 3) * S F := by
    simp only [generatingODE, map_add, map_sub, map_mul, map_pow, hSX,
      pow_one, map_ofNat, α, α']
    ring
  have h1 : powerSeriesEuler ℚ (S F) = S F.derivativeFun * powerSeriesEuler ℚ H := by
    simpa only [hS] using euler_subst F H hH0
  have h2 : powerSeriesEuler ℚ (powerSeriesEuler ℚ (S F)) =
      S F.derivativeFun.derivativeFun * (powerSeriesEuler ℚ H) ^ 2 +
        S F.derivativeFun * powerSeriesEuler ℚ (powerSeriesEuler ℚ H) := by
    simpa only [hS] using euler_subst_two F H hH0
  have hα : powerSeriesEuler ℚ α = α' * powerSeriesEuler ℚ H := by
    have h1 : powerSeriesEuler ℚ (1 : PowerSeries ℚ) = 0 :=
      (powerSeriesEuler ℚ).map_natCast 1
    have h10 : powerSeriesEuler ℚ (10 : PowerSeries ℚ) = 0 :=
      (powerSeriesEuler ℚ).map_natCast 10
    have h9 : powerSeriesEuler ℚ (9 : PowerSeries ℚ) = 0 :=
      (powerSeriesEuler ℚ).map_natCast 9
    simp only [α, α', Derivation.leibniz, map_sub, map_add, euler_sq,
      h1, h10, h9, smul_eq_mul]
    ring
  have hHH : powerSeriesEuler ℚ (powerSeriesEuler ℚ H) =
      α * α' * f ^ 4 + 2 * α * f * powerSeriesEuler ℚ f := by
    calc
      _ = powerSeriesEuler ℚ (α * f ^ 2) := congrArg (powerSeriesEuler ℚ) hH
      _ = α' * powerSeriesEuler ℚ H * f ^ 2 + α * (2 * f * powerSeriesEuler ℚ f) := by
        rw [Derivation.leibniz, hα, euler_sq]
        simp only [smul_eq_mul]
        ring
      _ = _ := by rw [hH]; ring
  have he : α * f ^ 5 * S (generatingODE F) =
      f ^ 2 * powerSeriesEuler ℚ (powerSeriesEuler ℚ V) := by
    calc
      _ = f * powerSeriesEuler ℚ (powerSeriesEuler ℚ (S F)) -
          2 * powerSeriesEuler ℚ f * powerSeriesEuler ℚ (S F) +
          α * (9 * H - 3) * f ^ 5 * S F := by
        rw [hODE, h2, hHH, h1, hH]
        ring
      _ = -(2 * (powerSeriesEuler ℚ f) ^ 2 -
          f * powerSeriesEuler ℚ (powerSeriesEuler ℚ f) -
          α * (9 * H - 3) * f ^ 6) * V +
            f ^ 2 * powerSeriesEuler ℚ (powerSeriesEuler ℚ V) := by
        rw [hS F, hcomp]
        simp only [Derivation.leibniz, map_add, smul_eq_mul]
        ring
      _ = _ := by rw [sub_eq_zero.mpr hf]; simp
  apply mul_left_cancel₀ (pow_ne_zero 2 hfne)
  calc
    _ = α * f ^ 5 * S (generatingODE F) := by rw [hS]; dsimp only [α]; ring
    _ = _ := he

end DirichletL

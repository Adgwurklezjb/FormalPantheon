import Analysis.ZagierODEPullback
import Analysis.ZagierDescendedODE

/-!
The all-index formal equation `explicitode` in CDT v2 for the actual descent
of `H_A`. The proof combines the source and conjugate second-order equations
with exact polynomial chain-rule certificates.
-/

namespace DirichletL

private theorem conjugateJet_identity {K : Type*} [Field K]
    (x u f0 f1 f2 : K) (hu : (x - 1) * u = -1) :
    x * (x - 1) ^ 2 * (8 * x + 1) * (f2 * u ^ 4 - 2 * f1 * u ^ 3) +
      (x - 1) * (8 * x ^ 2 - 16 * x - 1) * (-f1 * u ^ 2) +
      3 * (2 * x + 1) * f0 =
    (x - 1) * ((1 - u) * (1 - 10 * (1 - u) + 9 * (1 - u) ^ 2) * f2 +
      (1 - 20 * (1 - u) + 27 * (1 - u) ^ 2) * f1 + (9 * (1 - u) - 3) * f0) := by
  have hx : x - 1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hu
    exact one_ne_zero (neg_eq_zero.mp hu.symm)
  have hu' : u = -1 / (x - 1) := (eq_div_iff hx).mpr (by simpa [mul_comm] using hu)
  generalize ht : x - 1 = t at *
  have hxt : x = t + 1 := by linear_combination ht
  subst x
  rw [hu']
  field_simp [hx]
  ring

set_option maxHeartbeats 1600000 in
theorem zagierPullbackJet_chain {K : Type*} [Field K] [Algebra ℚ K]
    (x u g0 g1 g2 g3 g4 : K) (hu : (x - 1) * u = -1) :
    zagierPullbackJet x g0 (g1 * (1 - u ^ 2))
      (g2 * (1 - u ^ 2) ^ 2 + g1 * (-2 * u ^ 3))
      (g3 * (1 - u ^ 2) ^ 3 + 3 * g2 * (1 - u ^ 2) * (-2 * u ^ 3) +
        g1 * (-6 * u ^ 4))
      (g4 * (1 - u ^ 2) ^ 4 + 6 * g3 * (1 - u ^ 2) ^ 2 * (-2 * u ^ 3) +
        g2 * (3 * (-2 * u ^ 3) ^ 2 + 4 * (1 - u ^ 2) * (-6 * u ^ 4)) +
        g1 * (-24 * u ^ 5)) =
    (x - 1) ^ 3 *
      (Polynomial.aeval (x + (1 - u)) (zagierODECoeffQ 0) * g0 +
        Polynomial.aeval (x + (1 - u)) (zagierODECoeffQ 1) * g1 +
        Polynomial.aeval (x + (1 - u)) (zagierODECoeffQ 2) * g2 +
        Polynomial.aeval (x + (1 - u)) (zagierODECoeffQ 3) * g3 +
        Polynomial.aeval (x + (1 - u)) (zagierODECoeffQ 4) * g4) := by
  have hx : x - 1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hu
    exact one_ne_zero (neg_eq_zero.mp hu.symm)
  have hu' : u = -1 / (x - 1) := (eq_div_iff hx).mpr (by simpa [mul_comm] using hu)
  generalize ht : x - 1 = t at *
  have hxt : x = t + 1 := by linear_combination ht
  subst x
  rw [hu']
  simp only [zagierPullbackJet, zagierODECoeffQ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, map_mul, map_sub, map_add, map_neg, map_pow,
    map_ofNat, map_one, Polynomial.aeval_X]
  field_simp [hx]
  ring

local notation "D" => PowerSeries.derivative ℚ
local notation "x" => (PowerSeries.X : PowerSeries ℚ)
local notation "w" => mobiusInvolutionQ
local notation "K" => FractionRing (PowerSeries ℚ)
local notation "ι" => algebraMap (PowerSeries ℚ) K

private theorem fraction_mobius_unit : (ι x - 1) * (1 - ι w) = -1 := by
  have h := congrArg ι one_sub_X_mul_one_sub_mobiusInvolutionQ
  simp only [map_mul, map_sub, map_one] at h
  linear_combination -h

private theorem map_zagierPullbackJet {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (t f0 f1 f2 f3 f4 : R) :
    φ (zagierPullbackJet t f0 f1 f2 f3 f4) =
      zagierPullbackJet (φ t) (φ f0) (φ f1) (φ f2) (φ f3) (φ f4) := by
  simp only [zagierPullbackJet, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_one]

/-- Mobius substitution transports the full second-order forcing. -/
theorem zagierConjugateODE_subst_eq (f : PowerSeries ℚ) :
    zagierConjugateODE (MvPowerSeries.subst (fun (_ : Unit) => w) f) =
      (x - 1) * MvPowerSeries.subst (fun (_ : Unit) => w) (generatingODE f) := by
  have hw : MvPowerSeries.HasSubst (fun (_ : Unit) => w) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusInvolutionQ)
  let s := MvPowerSeries.substAlgHom (R := ℚ) (S := ℚ) hw
  have hX : s x = w := MvPowerSeries.substAlgHom_X hw ()
  have h0 : x * (1 - 10 * x + 9 * x ^ 2) * f.derivativeFun.derivativeFun +
      (1 - 20 * x + 27 * x ^ 2) * f.derivativeFun + (9 * x - 3) * f =
      generatingODE f := by
    simp only [generatingODE, map_ofNat, pow_one]
    ring
  have hs := congrArg s h0
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, map_zero, hX] at hs
  have hsf := congrArg ι hs
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, map_zero] at hsf
  apply IsFractionRing.injective (PowerSeries ℚ) K
  change ι (x * (x - 1) ^ 2 * (8 * x + 1) *
      PowerSeries.derivativeFun (PowerSeries.derivativeFun
        (MvPowerSeries.subst (fun (_ : Unit) => w) f)) +
    (x - 1) * (8 * x ^ 2 - 16 * x - 1) *
      PowerSeries.derivativeFun (MvPowerSeries.subst (fun (_ : Unit) => w) f) +
    3 * (2 * x + 1) * MvPowerSeries.subst (fun (_ : Unit) => w) f) =
      ι ((x - 1) * MvPowerSeries.subst (fun (_ : Unit) => w) (generatingODE f))
  rw [derivativeFun_subst_two f w constantCoeff_mobiusInvolutionQ,
    derivativeFun_subst f w constantCoeff_mobiusInvolutionQ]
  simp only [← MvPowerSeries.substAlgHom_apply hw]
  change ι (x * (x - 1) ^ 2 * (8 * x + 1) *
      (s (D (D f)) * (D w) ^ 2 + s (D f) * D (D w)) +
    (x - 1) * (8 * x ^ 2 - 16 * x - 1) * (s (D f) * D w) +
    3 * (2 * x + 1) * s f) = ι ((x - 1) * s (generatingODE f))
  rw [derivative_two_mobiusInvolutionQ, derivative_mobiusInvolutionQ]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one]
  have hc := conjugateJet_identity (ι x) (1 - ι w)
    (ι (s f)) (ι (s (D f))) (ι (s (D (D f)))) fraction_mobius_unit
  simp only [sub_sub_cancel] at hc
  have hs0 : (ι w * (1 - 10 * ι w + 9 * ι w ^ 2) * ι (s (D (D f))) +
      (1 - 20 * ι w + 27 * ι w ^ 2) * ι (s (D f)) +
      (9 * ι w - 3) * ι (s f)) = ι (s (generatingODE f)) := hsf
  rw [hs0] at hc
  linear_combination hc

/-- Substitution of a Zagier solution satisfies the conjugate second-order equation. -/
theorem zagierConjugateODE_subst {f : PowerSeries ℚ} (hf : generatingODE f = 0) :
    zagierConjugateODE (MvPowerSeries.subst (fun (_ : Unit) => w) f) = 0 := by
  have hw : MvPowerSeries.HasSubst (fun (_ : Unit) => w) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusInvolutionQ)
  rw [zagierConjugateODE_subst_eq, hf, ← MvPowerSeries.substAlgHom_apply hw,
    map_zero, mul_zero]

/-- The common fourth-order pullback annihilates the positive Zagier trace. -/
theorem zagierPullbackODE_symmetrizedFormal_hA :
    zagierPullbackODE (symmetrizedFormal hA) = 0 := by
  change zagierPullbackODE
    (hA + MvPowerSeries.subst (fun (_ : Unit) => w) hA) = 0
  rw [zagierPullbackODE_add, zagierPullbackODE_of_generatingODE hA_ode,
    zagierPullbackODE_of_conjugateODE (zagierConjugateODE_subst hA_ode), add_zero]

/-- The cleared polynomial chain rule for the full descended operator. -/
theorem zagierPullbackODE_subst (f : PowerSeries ℚ) :
    zagierPullbackODE (MvPowerSeries.subst (fun (_ : Unit) => mobiusCoordinateQ) f) =
      (x - 1) ^ 3 * MvPowerSeries.subst (fun (_ : Unit) => mobiusCoordinateQ)
        (zagierDescendedODE f) := by
  have hy : MvPowerSeries.HasSubst (fun (_ : Unit) => mobiusCoordinateQ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusCoordinateQ)
  let s := MvPowerSeries.substAlgHom (R := ℚ) (S := ℚ) hy
  have hp (i : Fin 5) : s (zagierODECoeffQ i : PowerSeries ℚ) =
      Polynomial.aeval mobiusCoordinateQ (zagierODECoeffQ i) := by
    rw [show s (zagierODECoeffQ i : PowerSeries ℚ) =
        MvPowerSeries.subst (fun (_ : Unit) => mobiusCoordinateQ)
          (zagierODECoeffQ i : PowerSeries ℚ) from MvPowerSeries.substAlgHom_apply hy _]
    exact subst_coe_polynomial_eq_aeval mobiusCoordinateQ constantCoeff_mobiusCoordinateQ _
  have hs : s (zagierDescendedODE f) =
      Polynomial.aeval mobiusCoordinateQ (zagierODECoeffQ 0) * s f +
        Polynomial.aeval mobiusCoordinateQ (zagierODECoeffQ 1) * s (D f) +
        Polynomial.aeval mobiusCoordinateQ (zagierODECoeffQ 2) * s (D (D f)) +
        Polynomial.aeval mobiusCoordinateQ (zagierODECoeffQ 3) * s (D (D (D f))) +
        Polynomial.aeval mobiusCoordinateQ (zagierODECoeffQ 4) * s (D (D (D (D f)))) := by
    change s ((zagierODECoeffQ 0 : PowerSeries ℚ) * f +
      (zagierODECoeffQ 1 : PowerSeries ℚ) * D f +
      (zagierODECoeffQ 2 : PowerSeries ℚ) * D (D f) +
      (zagierODECoeffQ 3 : PowerSeries ℚ) * D (D (D f)) +
      (zagierODECoeffQ 4 : PowerSeries ℚ) * D (D (D (D f)))) = _
    simp only [map_add, map_mul, hp]
  have hi (i : Fin 5) : ι (Polynomial.aeval mobiusCoordinateQ (zagierODECoeffQ i)) =
      Polynomial.aeval (ι mobiusCoordinateQ) (zagierODECoeffQ i) :=
    (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℚ (PowerSeries ℚ) K)
      mobiusCoordinateQ (zagierODECoeffQ i)).symm
  apply IsFractionRing.injective (PowerSeries ℚ) K
  simp only [← MvPowerSeries.substAlgHom_apply hy]
  change ι (zagierPullbackODE (s f)) = ι ((x - 1) ^ 3 * s (zagierDescendedODE f))
  rw [hs, zagierPullbackODE, MvPowerSeries.substAlgHom_apply hy]
  change ι (zagierPullbackJet x (MvPowerSeries.subst
    (fun (_ : Unit) => mobiusCoordinateQ) f)
    (PowerSeries.derivativeFun (MvPowerSeries.subst
      (fun (_ : Unit) => mobiusCoordinateQ) f))
    (PowerSeries.derivativeFun (PowerSeries.derivativeFun (MvPowerSeries.subst
      (fun (_ : Unit) => mobiusCoordinateQ) f)))
    (PowerSeries.derivativeFun (PowerSeries.derivativeFun (PowerSeries.derivativeFun
      (MvPowerSeries.subst (fun (_ : Unit) => mobiusCoordinateQ) f))))
    (PowerSeries.derivativeFun (PowerSeries.derivativeFun (PowerSeries.derivativeFun
      (PowerSeries.derivativeFun (MvPowerSeries.subst
        (fun (_ : Unit) => mobiusCoordinateQ) f)))))) = _
  rw [derivativeFun_subst_four f mobiusCoordinateQ constantCoeff_mobiusCoordinateQ,
    derivativeFun_subst_three f mobiusCoordinateQ constantCoeff_mobiusCoordinateQ,
    derivativeFun_subst_two f mobiusCoordinateQ constantCoeff_mobiusCoordinateQ,
    derivativeFun_subst f mobiusCoordinateQ constantCoeff_mobiusCoordinateQ]
  simp only [← MvPowerSeries.substAlgHom_apply hy]
  change ι (zagierPullbackJet x (s f)
    (s (D f) * D mobiusCoordinateQ)
    (s (D (D f)) * (D mobiusCoordinateQ) ^ 2 + s (D f) * D (D mobiusCoordinateQ))
    (s (D (D (D f))) * (D mobiusCoordinateQ) ^ 3 +
      3 * s (D (D f)) * D mobiusCoordinateQ * D (D mobiusCoordinateQ) +
      s (D f) * D (D (D mobiusCoordinateQ)))
    (s (D (D (D (D f)))) * (D mobiusCoordinateQ) ^ 4 +
      6 * s (D (D (D f))) * (D mobiusCoordinateQ) ^ 2 * D (D mobiusCoordinateQ) +
      s (D (D f)) * (3 * (D (D mobiusCoordinateQ)) ^ 2 +
        4 * D mobiusCoordinateQ * D (D (D mobiusCoordinateQ))) +
      s (D f) * D (D (D (D mobiusCoordinateQ))))) = _
  rw [derivative_four_mobiusCoordinateQ, derivative_three_mobiusCoordinateQ,
    derivative_two_mobiusCoordinateQ, derivative_mobiusCoordinateQ, map_zagierPullbackJet]
  simp only [map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one, hi]
  have hc := zagierPullbackJet_chain (ι x) (1 - ι w) (ι (s f)) (ι (s (D f)))
    (ι (s (D (D f)))) (ι (s (D (D (D f))))) (ι (s (D (D (D (D f))))))
    fraction_mobius_unit
  simpa only [sub_sub_cancel, mobiusCoordinateQ, map_add] using hc

/-- CDT v2 equation `explicitode` for the descended Zagier series, in every degree. -/
theorem zagierDescendedODE_symmetrizedDescent_hA :
    zagierDescendedODE (symmetrizedDescent hA) = 0 := by
  have h := zagierPullbackODE_subst (symmetrizedDescent hA)
  rw [subst_symmetrizedDescent, zagierPullbackODE_symmetrizedFormal_hA] at h
  have hx : x - 1 ≠ 0 := by
    intro h0
    have := congrArg (PowerSeries.constantCoeff (R := ℚ)) h0
    norm_num at this
  have hz := (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero 3 hx)
  apply subst_mobiusCoordinateQ_injective
  rw [hz]
  symm
  rw [← MvPowerSeries.substAlgHom_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun (_ : Unit) => constantCoeff_mobiusCoordinateQ))]
  exact map_zero _

end DirichletL

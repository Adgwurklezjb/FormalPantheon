import Analysis.ZagierDescentEquation
import Analysis.ZagierForcingPolynomials
import Analysis.FunctionsHFormalODE

/-!
The literal rational H combination satisfies a forced version of CDT v2
equation `explicitode`. The forcing follows from Lemma `defabc` and
Proposition `functionsH`, supplied TeX 7690-7751 and 8125-8140.
-/

namespace DirichletL

local notation "D" => PowerSeries.derivative ℚ
local notation "x" => (PowerSeries.X : PowerSeries ℚ)
local notation "w" => mobiusInvolutionQ
local notation "u" => (1 - mobiusInvolutionQ)
local notation "K" => FractionRing (PowerSeries ℚ)
local notation "ι" => algebraMap (PowerSeries ℚ) K

theorem zagierDescendedODE_symmetrizedDescent_of_forcing
    (f : PowerSeries ℚ) (b c : ℚ)
    (hf : generatingODE f = PowerSeries.C (R := ℚ) b + PowerSeries.C (R := ℚ) c * u) :
    zagierDescendedODE (symmetrizedDescent f) =
      b • (zagierDescendedForcingB : PowerSeries ℚ) +
        c • (zagierDescendedForcingC : PowerSeries ℚ) := by
  let r : PowerSeries ℚ := PowerSeries.C (R := ℚ) b + PowerSeries.C (R := ℚ) c * u
  have hd : D r = PowerSeries.C (R := ℚ) c * u ^ 2 := by
    dsimp [r]
    simp only [map_add, map_sub, PowerSeries.derivative_C, Derivation.leibniz,
      Derivation.map_one_eq_zero, derivative_mobiusInvolutionQ, smul_eq_mul]
    ring
  have hdd : D (D r) = 2 * PowerSeries.C (R := ℚ) c * u ^ 3 := by
    rw [hd]
    simp only [Derivation.leibniz, PowerSeries.derivative_C, Derivation.leibniz_pow,
      map_sub, Derivation.map_one_eq_zero, derivative_mobiusInvolutionQ,
      smul_eq_mul, nsmul_eq_mul]
    norm_num
    ring
  let rho : PowerSeries ℚ :=
    PowerSeries.C (R := ℚ) b * (x - 1) - PowerSeries.C (R := ℚ) c * (x - 1) ^ 2
  have hrd : D rho = PowerSeries.C (R := ℚ) b - 2 * PowerSeries.C (R := ℚ) c * (x - 1) := by
    dsimp [rho]
    simp only [map_sub, PowerSeries.derivative_C, Derivation.leibniz,
      Derivation.leibniz_pow, PowerSeries.derivative_X, Derivation.map_one_eq_zero,
      smul_eq_mul, nsmul_eq_mul]
    norm_num
    ring
  have hrdd : D (D rho) = -2 * PowerSeries.C (R := ℚ) c := by
    have h2 : D (2 : PowerSeries ℚ) = 0 := (PowerSeries.derivative ℚ).map_natCast 2
    rw [hrd]
    simp only [map_sub, PowerSeries.derivative_C, Derivation.leibniz,
      PowerSeries.derivative_X, Derivation.map_one_eq_zero, h2, smul_eq_mul]
    ring
  have hw : MvPowerSeries.HasSubst (fun (_ : Unit) => w) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusInvolutionQ)
  let s := MvPowerSeries.substAlgHom (R := ℚ) (S := ℚ) hw
  have hsw : s w = x := (MvPowerSeries.substAlgHom_apply hw w).trans
    mobiusInvolutionQ_subst_self
  have hsC (a : ℚ) : s (PowerSeries.C (R := ℚ) a) = PowerSeries.C (R := ℚ) a := s.commutes a
  have hconj : zagierConjugateODE (MvPowerSeries.subst (fun (_ : Unit) => w) f) = rho := by
    rw [zagierConjugateODE_subst_eq, hf, ← MvPowerSeries.substAlgHom_apply hw]
    change (x - 1) * s (PowerSeries.C (R := ℚ) b + PowerSeries.C (R := ℚ) c * u) = rho
    simp only [map_add, map_mul, map_sub, map_one, hsC, hsw]
    dsimp [rho]
    ring
  have hsource := zagierPullbackODE_eq_of_generatingODE hf
  rw [show D (D (PowerSeries.C (R := ℚ) b + PowerSeries.C (R := ℚ) c * u)) =
      2 * PowerSeries.C (R := ℚ) c * u ^ 3 from hdd,
    show D (PowerSeries.C (R := ℚ) b + PowerSeries.C (R := ℚ) c * u) =
      PowerSeries.C (R := ℚ) c * u ^ 2 from hd] at hsource
  have hconjSource := X_sub_one_mul_zagierPullbackODE_eq hconj
  rw [hrdd, hrd] at hconjSource
  have h := zagierPullbackODE_subst (symmetrizedDescent f)
  rw [subst_symmetrizedDescent] at h
  change zagierPullbackODE (f + MvPowerSeries.subst (fun (_ : Unit) => w) f) = _ at h
  rw [zagierPullbackODE_add] at h
  have ht : (x - 1) ^ 4 * MvPowerSeries.subst (fun (_ : Unit) => mobiusCoordinateQ)
      (zagierDescendedODE (symmetrizedDescent f)) =
      (x - 1) * zagierPullbackODE f +
        (x - 1) * zagierPullbackODE (MvPowerSeries.subst (fun (_ : Unit) => w) f) := by
    linear_combination -(x - 1) * h
  have hx : x - 1 ≠ 0 := by
    intro hz
    have h0 := congrArg (PowerSeries.constantCoeff (R := ℚ)) hz
    norm_num at h0
  have hy : MvPowerSeries.HasSubst (fun (_ : Unit) => mobiusCoordinateQ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusCoordinateQ)
  let t := MvPowerSeries.substAlgHom (R := ℚ) (S := ℚ) hy
  have htC (a : ℚ) : t (PowerSeries.C (R := ℚ) a) = PowerSeries.C (R := ℚ) a := t.commutes a
  have hp (P : Polynomial ℚ) : t (P : PowerSeries ℚ) =
      Polynomial.aeval mobiusCoordinateQ P := by
    rw [MvPowerSeries.substAlgHom_apply]
    exact subst_coe_polynomial_eq_aeval mobiusCoordinateQ constantCoeff_mobiusCoordinateQ P
  have hi (P : Polynomial ℚ) : ι (Polynomial.aeval mobiusCoordinateQ P) =
      Polynomial.aeval (ι mobiusCoordinateQ) P :=
    (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℚ (PowerSeries ℚ) K)
      mobiusCoordinateQ P).symm
  apply subst_mobiusCoordinateQ_injective
  apply mul_left_cancel₀ (pow_ne_zero 4 hx)
  rw [ht, hsource, hconjSource, PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul,
    ← MvPowerSeries.substAlgHom_apply hy]
  change _ = (x - 1) ^ 4 * t
    (PowerSeries.C (R := ℚ) b * (zagierDescendedForcingB : PowerSeries ℚ) +
      PowerSeries.C (R := ℚ) c * (zagierDescendedForcingC : PowerSeries ℚ))
  simp only [map_add, map_mul, htC, hp]
  apply IsFractionRing.injective (PowerSeries ℚ) K
  dsimp only [rho]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, hi]
  have hu : (ι x - 1) * (1 - ι w) = -1 := by
    have hunit := congrArg ι one_sub_X_mul_one_sub_mobiusInvolutionQ
    simp only [map_mul, map_sub, map_one] at hunit
    linear_combination -hunit
  simpa only [sub_sub_cancel, mobiusCoordinateQ, map_add] using
    zagierForcedTrace_identity (ι x) (1 - ι w) (ι (PowerSeries.C (R := ℚ) b))
      (ι (PowerSeries.C (R := ℚ) c)) hu

theorem zagierDescendedODE_symmetrizedDescent_h_linearCombination (a b c : ℚ) :
    zagierDescendedODE (symmetrizedDescent (a • hA + b • hB + c • hC)) =
      b • (zagierDescendedForcingB : PowerSeries ℚ) +
        c • (zagierDescendedForcingC : PowerSeries ℚ) := by
  apply zagierDescendedODE_symmetrizedDescent_of_forcing
  rw [generatingODE_h_linearCombination]
  have hx : (1 - x : PowerSeries ℚ) ≠ 0 := by
    intro hz
    have h0 := congrArg (PowerSeries.constantCoeff (R := ℚ)) hz
    norm_num at h0
  have hu : (PowerSeries.mk 1 : PowerSeries ℚ) = u := by
    apply mul_left_cancel₀ hx
    rw [one_sub_X_mul_one_sub_mobiusInvolutionQ]
    simpa only [mul_comm] using PowerSeries.mk_one_mul_one_sub_eq_one ℚ
  rw [← hu]
  ext n
  by_cases hn : n = 0
  · subst n
    simp [generatingSeries]
  · simp [generatingSeries, PowerSeries.coeff_C, hn]

end DirichletL

import Analysis.FunctionProductIndependence
import Analysis.PowerSeriesPolynomialIndependence
import Analysis.PowerSeriesCoordinates

/-!
Independence of the literal multivariate monomial templates in
CDT v2, supplied TeX 2910-2935 and 3965-3998.
-/

namespace DirichletL

open scoped Classical

theorem linearIndependent_prod_powerSeriesInVariable {K ι : Type*} [Field K] [Fintype ι]
    {f : ι → PowerSeries K} (hf : LinearIndependent K f) (d : ℕ) :
    LinearIndependent K (fun σ : Fin d → ι =>
      ∏ j, powerSeriesInVariable K j (f (σ j))) := by
  have hi := linearIndependent_fin_product (linearIndependent_powerSeries_coefficients hf) d
  apply Fintype.linearIndependent_iff.mpr
  intro c hc σ
  apply Fintype.linearIndependent_iff.mp hi c ?_ σ
  funext n
  have hn := congrArg (MvPowerSeries.coeff (R := K) (Finsupp.equivFunOnFinite.symm n)) hc
  simpa only [map_sum, map_smul, map_zero, coeff_prod_powerSeriesInVariable,
    Finsupp.coe_equivFunOnFinite_symm, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] using hn

theorem linearIndependent_shifted_prod_powerSeries {K ι : Type*} [Field K] [Fintype ι]
    (f : ι → PowerSeries K)
    (hf : ∀ P : ι → Polynomial K, ∑ i, (P i : PowerSeries K) * f i = 0 → P = 0)
    (d D : ℕ) :
    LinearIndependent K (fun p : (Fin d → ι) × (Fin d → Fin D) =>
      MvPowerSeries.monomial (R := K) (Finsupp.equivFunOnFinite.symm (fun j => (p.2 j).val)) 1 *
        ∏ j, powerSeriesInVariable K j (f (p.1 j))) := by
  have hi := linearIndependent_prod_powerSeriesInVariable
    (linearIndependent_shifted_powerSeries f hf D) d
  let e := Equiv.arrowProdEquivProdArrow (Fin d) (fun _ => ι) (fun _ => Fin D)
  have hp : LinearIndependent K (fun p : (Fin d → ι) × (Fin d → Fin D) =>
      ∏ j, powerSeriesInVariable K j (PowerSeries.monomial (R := K) (p.2 j).val 1 * f (p.1 j))) :=
    hi.comp e.symm e.symm.injective
  simpa only [prod_powerSeriesInVariable_shift] using hp

end DirichletL

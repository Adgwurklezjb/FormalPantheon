import Analysis.Hauptmodul

/-!
Coefficientwise algebra and summation for the formal q-series in CDT v2
Section 11.1. These lemmas use Mathlib's existing power-series topology
and the project's finite-product stabilization. They support the Euler
and Jacobi product arguments in Lau-Lee-Ono v3, Sections 3.5 and 4.1.
-/

namespace DirichletL

variable {R : Type*} [CommRing R]

theorem formalProduct_one : formalProduct (fun _ => (1 : PowerSeries R)) = 1 := by
  apply PowerSeries.ext
  intro n
  rw [coeff_formalProduct, formalProductCoeff]
  simp

theorem formalProduct_mul {f g : ℕ → PowerSeries R}
    (hf : ∀ i, PowerSeries.X ^ (i + 1) ∣ f i - 1)
    (hg : ∀ i, PowerSeries.X ^ (i + 1) ∣ g i - 1) :
    formalProduct f * formalProduct g = formalProduct (fun i => f i * g i) := by
  apply PowerSeries.ext
  intro n
  calc
    _ = PowerSeries.coeff (R := R) n
        ((∏ i ∈ Finset.range (n + 1), f i) * (∏ i ∈ Finset.range (n + 1), g i)) := by
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [coeff_formalProduct, coeff_formalProduct,
        coeff_formalProduct_stable hf (Finset.antidiagonal.fst_le hp),
        coeff_formalProduct_stable hg (Finset.antidiagonal.snd_le hp)]
    _ = _ := by
      rw [coeff_formalProduct, formalProductCoeff, Finset.prod_mul_distrib]

theorem formalProduct_pow {f : ℕ → PowerSeries R}
    (hf : ∀ i, PowerSeries.X ^ (i + 1) ∣ f i - 1) (m : ℕ) :
    formalProduct f ^ m = formalProduct (fun i => f i ^ m) := by
  induction m with
  | zero => simp only [pow_zero, formalProduct_one]
  | succ m ih =>
    calc
      _ = formalProduct (fun i => f i ^ m) * formalProduct f := by rw [pow_succ, ih]
      _ = formalProduct (fun i => f i ^ m * f i) :=
        formalProduct_mul (fun i => dvd_pow_sub_one_of_dvd_sub_one (hf i) m) hf
      _ = _ := by simp only [pow_succ]

open scoped PowerSeries.WithPiTopology

variable [TopologicalSpace R]

theorem hasSum_powerSeries_iff_coeff {ι : Type*} {f : ι → PowerSeries R} {s : PowerSeries R} :
    HasSum f s ↔ ∀ n, HasSum (fun i => PowerSeries.coeff (R := R) n (f i)) (PowerSeries.coeff (R := R) n s) := by
  simp only [HasSum, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto, map_sum]

theorem hasSum_powerSeries_of_finite_coeff {ι : Type*} (f : ι → PowerSeries R)
    (s : ℕ → Finset ι) (h : ∀ n i, i ∉ s n → PowerSeries.coeff (R := R) n (f i) = 0) :
    HasSum f (PowerSeries.mk (fun n => ∑ i ∈ s n, PowerSeries.coeff (R := R) n (f i))) := by
  rw [hasSum_powerSeries_iff_coeff]
  intro n
  rw [PowerSeries.coeff_mk]
  exact hasSum_sum_of_ne_finset_zero (h n)

theorem hasSum_powerSeries_of_X_pow_dvd {f : ℕ → PowerSeries R}
    (hf : ∀ i, PowerSeries.X ^ i ∣ f i) :
    HasSum f (PowerSeries.mk (fun n =>
      ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff (R := R) n (f i))) := by
  apply hasSum_powerSeries_of_finite_coeff
  intro n i hi
  have hni : n < i := by simp only [Finset.mem_range] at hi; omega
  exact PowerSeries.X_pow_dvd_iff.mp (hf i) n hni

theorem summable_powerSeries_of_finite_coeff {ι : Type*} (f : ι → PowerSeries R)
    (s : ℕ → Finset ι) (h : ∀ n i, i ∉ s n → PowerSeries.coeff (R := R) n (f i) = 0) :
    Summable f :=
  (hasSum_powerSeries_of_finite_coeff f s h).summable

end DirichletL

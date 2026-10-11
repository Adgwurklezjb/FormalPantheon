import Arithmetic.PowerSeriesEuler
import Analysis.Hauptmodul

/-!
Coefficientwise differentiation of the stabilized product used in CDT v2,
Section 11.1, equation `haupt` (TeX lines 7619-7637).
-/

namespace DirichletL

variable {R : Type*} [CommRing R]

theorem powerSeriesEuler_formalProduct {f g : ℕ → PowerSeries R} {G : PowerSeries R}
    (hf : ∀ i, PowerSeries.X ^ (i + 1) ∣ f i - 1)
    (hder : ∀ i, powerSeriesEuler R (f i) = f i * g i)
    (hG : ∀ n N, n ≤ N → PowerSeries.coeff (R := R) n G =
      ∑ i ∈ Finset.range (N + 1), PowerSeries.coeff (R := R) n (g i)) :
    powerSeriesEuler R (formalProduct f) = formalProduct f * G := by
  ext n
  let F := ∏ i ∈ Finset.range (n + 1), f i
  let Q := ∑ i ∈ Finset.range (n + 1), g i
  have hc (m : ℕ) (hm : m ≤ n) :
      PowerSeries.coeff (R := R) m F = PowerSeries.coeff (R := R) m (formalProduct f) := by
    rw [coeff_formalProduct]
    exact coeff_formalProduct_stable hf hm
  have hQ (m : ℕ) (hm : m ≤ n) :
      PowerSeries.coeff (R := R) m Q = PowerSeries.coeff (R := R) m G := by
    simp only [Q, map_sum]
    exact (hG m n hm).symm
  have hF : powerSeriesEuler R F = F * Q :=
    powerSeriesEuler_prod_of_eq _ (fun i _ => hder i)
  rw [coeff_powerSeriesEuler, ← hc n le_rfl, ← coeff_powerSeriesEuler F n,
    hF, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hc p.1 (Finset.antidiagonal.fst_le hp), hQ p.2 (Finset.antidiagonal.snd_le hp)]

end DirichletL

import Arithmetic.CoefficientDenominators
import Analysis.AuxiliaryFormalSeries
import Analysis.AuxiliaryExponentStatistics

/-!
Meanings, native interfaces, and endpoint checks precede these bodies in
CDT v2, supplied TeX 3965-3998, 4304-4404, and 4440-4518.
-/

namespace DirichletL

open scoped Classical

theorem isInteger_cdt14CoefficientDenominator_mul_prod_fin (h D : ℕ) {ρ δ : ℝ}
    (hρ : 0 ≤ 2 + ρ) (s : Fin (14 * h) → Fin 14)
    (hs : ∀ i : Fin 14, (Finset.univ.filter (fun j : Fin (14 * h) => s j = i)).card = h)
    (n r : Fin (14 * h) → ℕ) (q : Fin (14 * h) → ℚ)
    (hn : ∀ j, (n j : ℝ) ≤ D * (δ + ((j : ℝ) + 1) / h))
    (hlo : ∀ j, n j - D ≤ r j) (hhi : ∀ j, r j ≤ n j)
    (hzero : ∀ j, r j = 0 → IsLocalization.IsInteger ℤ (q j))
    (hcoeff : ∀ j, IsLocalization.IsInteger ℤ
      ((cdtHolonomyPerturbedMultiplier ρ (s j) (r j) : ℚ) * q j)) :
    IsLocalization.IsInteger ℤ
      ((cdt14CoefficientDenominator h D ρ δ
        (Function.extend Fin.val n (fun _ => 0)) : ℚ) * ∏ j, q j) := by
  let s' := Function.extend Fin.val s (fun _ : ℕ => (0 : Fin 14))
  let n' := Function.extend Fin.val n (fun _ : ℕ => 0)
  let r' := Function.extend Fin.val r (fun _ : ℕ => 0)
  let q' := Function.extend Fin.val q (fun _ : ℕ => 0)
  have hes (j : Fin (14 * h)) : s' j = s j := Fin.val_injective.extend_apply _ _ j
  have hen (j : Fin (14 * h)) : n' j = n j := Fin.val_injective.extend_apply _ _ j
  have her (j : Fin (14 * h)) : r' j = r j := Fin.val_injective.extend_apply _ _ j
  have heq (j : Fin (14 * h)) : q' j = q j := Fin.val_injective.extend_apply _ _ j
  have hs' (i : Fin 14) :
      (Finset.univ.filter (fun j : Fin (14 * h) => s' (j : ℕ) = i)).card = h := by
    simpa only [hes] using hs i
  have hn' (j : ℕ) (hj : j < 14 * h) :
      (n' j : ℝ) ≤ D * (δ + ((j : ℝ) + 1) / h) := by
    change (n' (⟨j, hj⟩ : Fin (14 * h)) : ℝ) ≤ _
    rw [hen]
    exact hn ⟨j, hj⟩
  have hlo' (j : ℕ) (hj : j < 14 * h) : n' j - D ≤ r' j := by
    change n' (⟨j, hj⟩ : Fin (14 * h)) - D ≤ r' (⟨j, hj⟩ : Fin (14 * h))
    rw [hen, her]
    exact hlo ⟨j, hj⟩
  have hhi' (j : ℕ) (hj : j < 14 * h) : r' j ≤ n' j := by
    change r' (⟨j, hj⟩ : Fin (14 * h)) ≤ n' (⟨j, hj⟩ : Fin (14 * h))
    rw [her, hen]
    exact hhi ⟨j, hj⟩
  have hz' (j : ℕ) (hj : j < 14 * h) :
      r' j = 0 → IsLocalization.IsInteger ℤ (q' j) := by
    change r' (⟨j, hj⟩ : Fin (14 * h)) = 0 →
      IsLocalization.IsInteger ℤ (q' (⟨j, hj⟩ : Fin (14 * h)))
    rw [her, heq]
    exact hzero ⟨j, hj⟩
  have hc' (j : ℕ) (hj : j < 14 * h) : IsLocalization.IsInteger ℤ
      ((cdtHolonomyPerturbedMultiplier ρ (s' j) (r' j) : ℚ) * q' j) := by
    change IsLocalization.IsInteger ℤ
      ((cdtHolonomyPerturbedMultiplier ρ (s' (⟨j, hj⟩ : Fin (14 * h)))
        (r' (⟨j, hj⟩ : Fin (14 * h))) : ℚ) * q' (⟨j, hj⟩ : Fin (14 * h)))
    rw [hes, her, heq]
    exact hcoeff ⟨j, hj⟩
  have hc := isInteger_cdt14CoefficientDenominator_mul_prod h D hρ s' hs'
    n' r' q' hn' hlo' hhi' hz' hc'
  simpa only [Finset.prod_range, heq] using hc

theorem isInteger_cdt14CoefficientDenominator_mul_auxiliary_coeff
    (f : Fin 14 → PowerSeries ℚ) (h D : ℕ) (ε : ℝ) {ρ δ : ℝ}
    (hρ : 0 ≤ 2 + ρ)
    (hzero : ∀ i, IsLocalization.IsInteger ℤ (PowerSeries.coeff (R := ℚ) 0 (f i)))
    (hcoeff : ∀ i r, IsLocalization.IsInteger ℤ
      ((cdtHolonomyPerturbedMultiplier ρ i r : ℚ) * PowerSeries.coeff (R := ℚ) r (f i)))
    (t : ↥(auxiliaryFreeIndices 14 h D ε) → ℤ) (n : Fin (14 * h) →₀ ℕ)
    (σ : Equiv.Perm (Fin (14 * h)))
    (hn : ∀ j, (n (σ j) : ℝ) ≤ D * (δ + ((j : ℝ) + 1) / h)) :
    IsLocalization.IsInteger ℤ
      ((cdt14CoefficientDenominator h D ρ δ
        (Function.extend Fin.val (fun j => n (σ j)) (fun _ => 0)) : ℚ) *
          MvPowerSeries.coeff (R := ℚ) n (auxiliaryFormalSeries f h D ε t)) := by
  rw [coeff_auxiliaryFormalSeries, Finset.mul_sum]
  apply (algebraMap ℤ ℚ).rangeS.sum_mem
  intro p _
  by_cases hk : ∀ j, (p.val.2 j).val ≤ n j
  · rw [if_pos hk]
    have hbal := (mem_auxiliaryFreeIndices.mp p.property).1
    have hbal' := balancedSpeciesIndices_comp_perm hbal σ
    have hs : ∀ i : Fin 14, (Finset.univ.filter
        (fun j : Fin (14 * h) => p.val.1 (σ j) = i)).card = h := by
      simpa only [balancedSpeciesIndices, Finset.mem_filter, Finset.mem_univ,
        true_and, Function.comp_apply] using hbal'
    have hc := isInteger_cdt14CoefficientDenominator_mul_prod_fin h D hρ
      (fun j => p.val.1 (σ j)) hs (fun j => n (σ j))
      (fun j => n (σ j) - (p.val.2 (σ j)).val)
      (fun j => PowerSeries.coeff (R := ℚ) (n (σ j) - (p.val.2 (σ j)).val) (f (p.val.1 (σ j))))
      hn (fun j => Nat.sub_le_sub_left (p.val.2 (σ j)).isLt.le (n (σ j)))
      (fun j => Nat.sub_le _ _)
      (fun j hj => by
        dsimp only at hj ⊢
        rw [hj]
        exact hzero _)
      (fun j => hcoeff _ _)
    have hp : (∏ j : Fin (14 * h),
        PowerSeries.coeff (R := ℚ) (n (σ j) - (p.val.2 (σ j)).val) (f (p.val.1 (σ j)))) =
        ∏ j, PowerSeries.coeff (R := ℚ) (n j - (p.val.2 j).val) (f (p.val.1 j)) :=
      Equiv.prod_comp σ (fun j => PowerSeries.coeff (R := ℚ) (n j - (p.val.2 j).val) (f (p.val.1 j)))
    rw [hp] at hc
    have ht := IsLocalization.isInteger_mul (show IsLocalization.IsInteger ℤ (t p : ℚ) from
      ⟨t p, by simp⟩) hc
    convert ht using 1
    ring
  · simp only [if_neg hk, mul_zero]
    exact IsLocalization.isInteger_zero

end DirichletL

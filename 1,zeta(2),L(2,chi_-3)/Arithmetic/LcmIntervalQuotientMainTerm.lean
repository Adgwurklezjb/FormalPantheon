import Arithmetic.LcmIntervalMainTerm
import Arithmetic.LcmIntervalQuotient

/-!
The clipped harmonic rate in CDT v2 Section 2.2, supplied TeX 3363-3411,
for the literal denominator quotient at TeX 4260-4283. Natural division
keeps the last gap index and the paper's denominator exactly aligned.
-/

namespace DirichletL

/-- The final potentially nonempty gap above the cutoff. -/
def lcmIntervalQuotientIndex (n k c : ℕ) : ℕ := (n - k) / max k c

/-- The clipped harmonic rate, with the zero-width convention made explicit. -/
noncomputable def lcmIntervalQuotientMainTerm (n k c : ℕ) : ℝ :=
  if k = 0 then 0 else
    (k : ℝ) * (harmonic (lcmIntervalQuotientIndex n k c) : ℝ) +
      max ((n : ℝ) / ((lcmIntervalQuotientIndex n k c : ℝ) + 1) - (c : ℝ)) 0

theorem lcmIntervalQuotientMainTerm_nonneg (n k c : ℕ) :
    0 ≤ lcmIntervalQuotientMainTerm n k c := by
  have hh : (0 : ℚ) ≤ harmonic (lcmIntervalQuotientIndex n k c) := by
    unfold harmonic
    exact Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  unfold lcmIntervalQuotientMainTerm
  split_ifs
  · exact le_rfl
  · exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Rat.cast_nonneg.mpr hh))
      (le_max_right _ _)

theorem lcmIntervalQuotientMainTerm_zero_width (n c : ℕ) :
    lcmIntervalQuotientMainTerm n 0 c = 0 := by
  simp [lcmIntervalQuotientMainTerm]

theorem lcmIntervalQuotientIndex_le {n k c : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    lcmIntervalQuotientIndex n k c ≤ n / k - 1 := by
  have hdiv := Nat.div_eq_sub_div hk hkn
  have hle : (n - k) / max k c ≤ (n - k) / k :=
    Nat.div_le_div_left (le_max_left k c) hk
  unfold lcmIntervalQuotientIndex
  omega

theorem lcmIntervalQuotientIndex_succ {n k c : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    lcmIntervalQuotientIndex n k c + 1 = (n + (c - k)) / max k c := by
  have hD : 0 < max k c := hk.trans_le (le_max_left _ _)
  have he : n + (c - k) = (n - k) + max k c := by omega
  rw [he, Nat.add_div_right _ hD]
  rfl

theorem lcmIntervalQuotientMainTerm_zero_cutoff {n k : ℕ} (hkn : k ≤ n) :
    lcmIntervalQuotientMainTerm n k 0 = lcmIntervalMainTerm n k := by
  by_cases hk : k = 0
  · subst k
    simp [lcmIntervalQuotientMainTerm, lcmIntervalMainTerm]
  · have hk0 : 0 < k := Nat.pos_of_ne_zero hk
    have hdiv := Nat.div_eq_sub_div hk0 hkn
    have hidx : lcmIntervalQuotientIndex n k 0 = n / k - 1 := by
      simp only [lcmIntervalQuotientIndex, max_eq_left (Nat.zero_le k)]
      rw [hdiv, Nat.add_sub_cancel]
    have hcast : ((lcmIntervalQuotientIndex n k 0 : ℕ) : ℝ) + 1 =
        ((n / k : ℕ) : ℝ) := by
      rw [hidx]
      exact_mod_cast Nat.sub_add_cancel (Nat.div_pos hkn hk0)
    rw [lcmIntervalQuotientMainTerm, if_neg hk, hcast, hidx, lcmIntervalMainTerm]
    simp only [Nat.cast_zero, sub_zero]
    rw [max_eq_left (show (0 : ℝ) ≤ (n : ℝ) / ((n / k : ℕ) : ℝ) by positivity)]

end DirichletL

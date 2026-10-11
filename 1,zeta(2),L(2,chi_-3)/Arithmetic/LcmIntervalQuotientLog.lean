import Arithmetic.LcmIntervalQuotient
import Arithmetic.LcmIntervalGaps

/-!
Exact cutoff-weighted prime-power sums for CDT v2 Section 2.2,
supplied TeX 3363-3430, and the literal gcd quotient at 4260-4283.
The cutoff is imposed on each prime power, including its multiplicity.
-/

namespace DirichletL

open scoped ArithmeticFunction.vonMangoldt

theorem log_gcd_lcmInterval_lcmPrefix (n k c : ℕ) :
    Real.log (Nat.gcd (lcmInterval n k) (lcmPrefix c) : ℝ) =
      ∑ q ∈ (Finset.range (n + 1)).filter (fun q => q ∣ lcmInterval n k ∧ q ≤ c), Λ q := by
  classical
  let g := Nat.gcd (lcmInterval n k) (lcmPrefix c)
  let S := (Finset.range (n + 1)).filter (fun q => q ∣ lcmInterval n k ∧ q ≤ c)
  have hg : g ≠ 0 := (Nat.gcd_pos_of_pos_left _ (lcmInterval_pos n k)).ne'
  have he : g.divisors.filter (fun q => Λ q ≠ 0) = S.filter (fun q => Λ q ≠ 0) := by
    ext q
    simp only [S, g, Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff,
      Finset.mem_range, ArithmeticFunction.vonMangoldt_ne_zero_iff]
    constructor
    · rintro ⟨⟨⟨hdL, hdP⟩, _⟩, hq⟩
      have hqn := (isPrimePow_dvd_lcmPrefix_iff hq).mp
        (hdL.trans (lcmInterval_dvd_lcmPrefix n k))
      exact ⟨⟨Nat.lt_succ_iff.mpr hqn, hdL, (isPrimePow_dvd_lcmPrefix_iff hq).mp hdP⟩, hq⟩
    · rintro ⟨⟨_, hdL, hqc⟩, hq⟩
      exact ⟨⟨⟨hdL, (isPrimePow_dvd_lcmPrefix_iff hq).mpr hqc⟩, hg⟩, hq⟩
  calc
    Real.log (g : ℝ) = ∑ q ∈ g.divisors, Λ q := ArithmeticFunction.vonMangoldt_sum.symm
    _ = ∑ q ∈ g.divisors.filter (fun q => Λ q ≠ 0), Λ q :=
      (Finset.sum_filter_ne_zero _).symm
    _ = ∑ q ∈ S.filter (fun q => Λ q ≠ 0), Λ q := by rw [he]
    _ = ∑ q ∈ S, Λ q := Finset.sum_filter_ne_zero _

theorem log_lcmIntervalQuotient_eq_sub (n k c : ℕ) :
    Real.log (lcmIntervalQuotient n k c : ℝ) = Real.log (lcmInterval n k : ℝ) -
      Real.log (Nat.gcd (lcmInterval n k) (lcmPrefix c) : ℝ) := by
  have hL : (lcmInterval n k : ℝ) ≠ 0 := by exact_mod_cast (lcmInterval_pos n k).ne'
  have hg : (Nat.gcd (lcmInterval n k) (lcmPrefix c) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left _ (lcmInterval_pos n k)).ne'
  rw [lcmIntervalQuotient, Nat.cast_div_charZero (Nat.gcd_dvd_left _ _), Real.log_div hL hg]

theorem log_lcmIntervalQuotient_eq_sum_vonMangoldt (n k c : ℕ) :
    Real.log (lcmIntervalQuotient n k c : ℝ) =
      ∑ q ∈ (Finset.range (n + 1)).filter (fun q => q ∣ lcmInterval n k ∧ c < q), Λ q := by
  classical
  let S := (Finset.range (n + 1)).filter (fun q => q ∣ lcmInterval n k)
  have hsplit : (∑ q ∈ S.filter (fun q => q ≤ c), Λ q) +
      (∑ q ∈ S.filter (fun q => ¬q ≤ c), Λ q) = ∑ q ∈ S, Λ q :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  dsimp only [S] at hsplit
  simp only [Finset.filter_filter, not_le] at hsplit
  rw [log_lcmIntervalQuotient_eq_sub, log_lcmInterval_eq_sum_vonMangoldt,
    log_gcd_lcmInterval_lcmPrefix]
  linarith

theorem sum_cutoff_missing_vonMangoldt_eq_sum_gaps (n k c : ℕ) (hk : 0 < k) :
    (∑ q ∈ (Finset.range (n + 1)).filter (fun q => c < q ∧ ¬q ∣ lcmInterval n k), Λ q) =
      ∑ a ∈ Finset.Icc 1 (n / k - 1),
        ∑ q ∈ (lcmIntervalGap n k a).filter (fun q => c < q), Λ q := by
  classical
  let S := (Finset.range (n + 1)).filter (fun q => c < q ∧ ¬q ∣ lcmInterval n k)
  let U := (Finset.Icc 1 (n / k - 1)).biUnion
    (fun a => (lcmIntervalGap n k a).filter (fun q => c < q))
  have he : S.filter (fun q => Λ q ≠ 0) = U.filter (fun q => Λ q ≠ 0) := by
    ext q
    simp only [S, Finset.mem_filter, Finset.mem_range,
      ArithmeticFunction.vonMangoldt_ne_zero_iff]
    constructor
    · rintro ⟨⟨hqn, hqc, hd⟩, hq⟩
      obtain ⟨a, ha, hqa⟩ := Finset.mem_biUnion.mp
        ((not_dvd_lcmInterval_iff_mem_biUnion hq (Nat.lt_succ_iff.mp hqn) hk).mp hd)
      exact ⟨Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_filter.mpr ⟨hqa, hqc⟩⟩, hq⟩
    · rintro ⟨hm, hq⟩
      obtain ⟨a, ha, hqa⟩ := Finset.mem_biUnion.mp hm
      have hqa' := Finset.mem_filter.mp hqa
      have hqn := (mem_lcmIntervalGap.mp hqa'.1).1
      have hd := (not_dvd_lcmInterval_iff_mem_biUnion hq hqn hk).mpr
        (Finset.mem_biUnion.mpr ⟨a, ha, hqa'.1⟩)
      exact ⟨⟨Nat.lt_succ_iff.mpr hqn, hqa'.2, hd⟩, hq⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 (n / k - 1)))
      (fun a => (lcmIntervalGap n k a).filter (fun q => c < q)) := by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro q hqa hqb
    exact Finset.disjoint_left.mp (lcmIntervalGap_disjoint hab)
      (Finset.mem_filter.mp hqa).1 (Finset.mem_filter.mp hqb).1
  calc
    (∑ q ∈ S, Λ q) = ∑ q ∈ S.filter (fun q => Λ q ≠ 0), Λ q :=
      (Finset.sum_filter_ne_zero _).symm
    _ = ∑ q ∈ U.filter (fun q => Λ q ≠ 0), Λ q := by rw [he]
    _ = ∑ q ∈ U, Λ q := Finset.sum_filter_ne_zero _
    _ = _ := Finset.sum_biUnion hdisj

theorem log_lcmIntervalQuotient_add_sum_gaps (n k c : ℕ) (hk : 0 < k) :
    Real.log (lcmIntervalQuotient n k c : ℝ) +
      (∑ a ∈ Finset.Icc 1 (n / k - 1),
        ∑ q ∈ (lcmIntervalGap n k a).filter (fun q => c < q), Λ q) =
          ∑ q ∈ (Finset.range (n + 1)).filter (fun q => c < q), Λ q := by
  classical
  rw [← sum_cutoff_missing_vonMangoldt_eq_sum_gaps n k c hk,
    log_lcmIntervalQuotient_eq_sum_vonMangoldt]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Finset.range (n + 1)).filter (fun q => c < q)) (fun q => q ∣ lcmInterval n k)
    (fun q => Λ q)
  simpa only [Finset.filter_filter, and_comm] using hsplit

end DirichletL

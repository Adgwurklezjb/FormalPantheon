import Analysis.UniformSequenceLimits
import Arithmetic.LcmAsymptotic

/-!
Uniform von Mangoldt errors for CDT v2 Section 2.2, supplied TeX
3330-3359. The canonical weak PNT controls all moving prefix endpoints,
and native floors and ceilings preserve the open interval convention.
-/

namespace DirichletL

open Filter
open scoped Topology ArithmeticFunction.vonMangoldt

theorem eventually_abs_sum_vonMangoldt_sub_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ m ≤ N,
      |(∑ q ∈ Finset.range m, Λ q) - (m : ℝ)| ≤ ε * (N : ℝ) := by
  simpa only [one_mul] using
    eventually_abs_initialSegment_sub_le tendsto_sum_vonMangoldt_div hε

theorem sum_vonMangoldt_Ioo_eq_Ico {N : ℕ} {u v : ℝ} (hu : 0 ≤ u) (hv : v ≤ (N : ℝ)) :
    (∑ q ∈ (Finset.range (N + 1)).filter (fun q : ℕ => u < (q : ℝ) ∧ (q : ℝ) < v), Λ q) =
      ∑ q ∈ Finset.Ico (⌊u⌋₊ + 1) ⌈v⌉₊, Λ q := by
  have hcast (q : ℕ) :
      u < (q : ℝ) ∧ (q : ℝ) < v ↔ ⌊u⌋₊ < q ∧ q < ⌈v⌉₊ := by
    change q ∈ (Nat.cast : ℕ → ℝ) ⁻¹' Set.Ioo u v ↔ q ∈ Set.Ioo ⌊u⌋₊ ⌈v⌉₊
    rw [Nat.preimage_Ioo hu]
  have he : (Finset.range (N + 1)).filter (fun q : ℕ => u < (q : ℝ) ∧ (q : ℝ) < v) =
      Finset.Ico (⌊u⌋₊ + 1) ⌈v⌉₊ := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨_, hq⟩
      have h := (hcast q).mp hq
      exact ⟨by omega, h.2⟩
    · rintro ⟨hlo, hhi⟩
      have hq := (hcast q).mpr ⟨by omega, hhi⟩
      have hqn : q ≤ N := by exact_mod_cast hq.2.le.trans hv
      exact ⟨by omega, hq⟩
  rw [he]

theorem abs_sum_vonMangoldt_Ico_sub_le {N : ℕ} {u v δ : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ (N : ℝ))
    (herr : ∀ m ≤ N, |(∑ q ∈ Finset.range m, Λ q) - (m : ℝ)| ≤ δ) :
    |(∑ q ∈ Finset.Ico (⌊u⌋₊ + 1) ⌈v⌉₊, Λ q) - (v - u)| ≤ 2 * δ + 2 := by
  have hv0 : 0 ≤ v := hu.trans huv.le
  have hAB : ⌊u⌋₊ + 1 ≤ ⌈v⌉₊ := by
    have h := Nat.floor_lt_ceil_of_lt_of_pos huv (hu.trans_lt huv)
    omega
  have hBN : ⌈v⌉₊ ≤ N := Nat.ceil_le.mpr hv
  have hA := abs_le.mp (herr (⌊u⌋₊ + 1) (hAB.trans hBN))
  have hB := abs_le.mp (herr ⌈v⌉₊ hBN)
  have hAlower : u ≤ ((⌊u⌋₊ + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one u).le
  have hAupper : ((⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ u + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using add_le_add_right (Nat.floor_le hu) 1
  have hBlower : v ≤ (⌈v⌉₊ : ℝ) := Nat.le_ceil _
  have hBupper : (⌈v⌉₊ : ℝ) ≤ v + 1 := (Nat.ceil_lt_add_one hv0).le
  rw [Finset.sum_Ico_eq_sub _ hAB]
  apply abs_le.mpr
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]

theorem eventually_abs_sum_vonMangoldt_Ico_sub_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ u v : ℝ, 0 ≤ u → v ≤ (N : ℝ) →
      |(∑ q ∈ Finset.Ico (⌊u⌋₊ + 1) ⌈v⌉₊, Λ q) - max (v - u) 0| ≤ ε * (N : ℝ) := by
  have hquarter : 0 < ε / 4 := by positivity
  filter_upwards [eventually_abs_sum_vonMangoldt_sub_le hquarter,
    eventually_ge_atTop ⌈4 / ε⌉₊] with N hN hNlarge u v hu hv
  by_cases huv : u < v
  · rw [max_eq_left (sub_nonneg.mpr huv.le)]
    have he := abs_sum_vonMangoldt_Ico_sub_le hu huv hv hN
    have hratio : 4 / ε ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNlarge)
    have hfour : (4 : ℝ) ≤ ε * (N : ℝ) := by
      have h := (div_le_iff₀ hε).mp hratio
      nlinarith
    exact he.trans (by nlinarith)
  · have hvu : v ≤ u := le_of_not_gt huv
    have hBA : ⌈v⌉₊ ≤ ⌊u⌋₊ + 1 := (Nat.ceil_mono hvu).trans (Nat.ceil_le_floor_add_one u)
    rw [Finset.Ico_eq_empty_of_le hBA, Finset.sum_empty, max_eq_right (sub_nonpos.mpr hvu),
      sub_self, abs_zero]
    exact mul_nonneg hε.le (Nat.cast_nonneg N)

end DirichletL

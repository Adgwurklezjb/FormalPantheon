import BoundedGaps.Foundations.Admissible
import Mathlib.Data.Fintype.Card

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-!
# The explicit 48-tuple of diameter 236

Source/provenance: <https://github.com/gotrevor/bounded_gaps>, commit
`2b888f757cd181eb75379560391c3db51b4473af`, file
`BoundedGaps/Engelsma.lean`, declaration `tuple_48`.

The source list is represented here as a `Finset ℕ` so that it uses
FormalPantheon's existing residue-cardinality definition of admissibility.
All finite computations in this module are kernel-checked with `decide`.
-/

namespace BoundedGaps.H1236

def engelsmaTuple48 : Finset ℕ :=
  [0, 6, 8, 14, 18, 24, 26, 48, 50, 54, 56, 60,
    66, 68, 74, 78, 80, 84, 90, 96, 98, 104, 110, 116,
    120, 126, 134, 138, 144, 150, 158, 164, 168, 176,
    180, 186, 188, 194, 200, 204, 206, 210, 216, 224,
    228, 230, 234, 236].toFinset

theorem engelsmaTuple48_card : engelsmaTuple48.card = 48 := by
  decide

theorem engelsmaTuple48_fintype_card : Fintype.card engelsmaTuple48 = 48 := by
  simpa only [Fintype.card_coe] using engelsmaTuple48_card

theorem engelsmaTuple48_mem_zero : 0 ∈ engelsmaTuple48 := by
  decide

theorem engelsmaTuple48_mem_236 : 236 ∈ engelsmaTuple48 := by
  decide

theorem engelsmaTuple48_le_236 {h : ℕ} (hh : h ∈ engelsmaTuple48) :
    h ≤ 236 := by
  simp [engelsmaTuple48] at hh
  omega

private theorem residue_card_lt_of_tuple_card_lt_prime {p : ℕ}
    (hcard : engelsmaTuple48.card < p) :
    (engelsmaTuple48.image (fun h => h % p)).card < p := by
  exact Finset.card_image_le.trans_lt hcard

theorem engelsmaTuple48_admissible :
    BoundedGaps.IsAdmissible engelsmaTuple48 := by
  intro p hp
  by_cases hsmall : p ≤ engelsmaTuple48.card
  · rw [engelsmaTuple48_card] at hsmall
    have hfinite : ∀ q ∈ Finset.range 49, q.Prime →
        (engelsmaTuple48.image (fun h => h % q)).card < q := by
      decide
    exact hfinite p (by simp [Nat.lt_succ_iff, hsmall]) hp
  · exact residue_card_lt_of_tuple_card_lt_prime (Nat.lt_of_not_ge hsmall)

theorem engelsmaTuple48_sorted_bounds :
    engelsmaTuple48.card = 48 ∧
      (∀ h ∈ engelsmaTuple48, h ≤ 236) ∧
      0 ∈ engelsmaTuple48 ∧ 236 ∈ engelsmaTuple48 := by
  exact ⟨engelsmaTuple48_card, (fun h hh => engelsmaTuple48_le_236 hh),
    engelsmaTuple48_mem_zero, engelsmaTuple48_mem_236⟩

end BoundedGaps.H1236

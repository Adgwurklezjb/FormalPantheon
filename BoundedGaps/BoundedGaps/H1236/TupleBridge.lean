import BoundedGaps.H1236.Statement
import BoundedGaps.H1236.Tuple48
import BoundedGaps.Proof.TupleBridge

/-!
# Transfer from prime shifts to a parameterized bounded-gap statement

This is the constant-parameterized counterpart of the elementary transfer in
`BoundedGaps.Proof.TupleBridge`. It does not supply an analytic prime-shift
result; it only converts such a result into the explicit prime-pair statement.
-/

namespace BoundedGaps.H1236

theorem boundedGapsStatementAt_of_two_prime_shifts {C : ℕ} {H : Finset ℕ}
    (hH : ∀ h ∈ H, h ≤ C)
    (hprime : BoundedGaps.InfinitelyOftenAtLeastPrimeShifts H 2) :
    boundedGapsStatementAt C := by
  intro N
  obtain ⟨n, hNn, hcount⟩ := hprime N
  have hcard : 1 < (H.filter fun h => (n + h).Prime).card := by
    unfold BoundedGaps.primeShiftCount at hcount
    omega
  obtain ⟨h₁, hh₁, h₂, hh₂, hne⟩ := Finset.one_lt_card.mp hcard
  have h₁data := Finset.mem_filter.mp hh₁
  have h₂data := Finset.mem_filter.mp hh₂
  have hpair :
      ∃ a b : ℕ, a ∈ H ∧ b ∈ H ∧ a < b ∧ (n + a).Prime ∧ (n + b).Prime := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨h₁, h₂, h₁data.1, h₂data.1, hlt, h₁data.2, h₂data.2⟩
    · exact ⟨h₂, h₁, h₂data.1, h₁data.1, hlt, h₂data.2, h₁data.2⟩
  obtain ⟨a, b, haH, hbH, hab, hpa, hpb⟩ := hpair
  refine ⟨n + a, n + b, ?_, ?_, hpa, hpb, ?_⟩
  · exact lt_of_lt_of_le hNn (Nat.le_add_right n a)
  · exact Nat.add_lt_add_left hab n
  · have hb := hH b hbH
    omega

/-- The verified diameter-236 tuple converts any two-prime-shift result into
the explicit bounded-gap-at-most-236 statement. -/
theorem boundedGapsStatement236_of_engelsmaTuple48_two_prime_shifts :
    BoundedGaps.InfinitelyOftenAtLeastPrimeShifts engelsmaTuple48 2 →
      boundedGapsStatement236 := by
  intro hprime
  apply boundedGapsStatementAt_of_two_prime_shifts
  · intro h hh
    exact engelsmaTuple48_le_236 hh
  · exact hprime

end BoundedGaps.H1236

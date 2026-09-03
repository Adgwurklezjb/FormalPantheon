import BoundedGaps.Proof.LiminfBridge

/-!
# Public constant-parameterized bounded-gaps statements

This module separates the prospective bound 236 from the existing public
constant-600 statement. It contains only elementary statement equivalences and
uses the existing prime-gap sequence from `BoundedGaps.Statement`.
-/

namespace BoundedGaps.H1236

/-- Arbitrarily large prime pairs whose difference is at most `C`. -/
def boundedGapsStatementAt (C : ℕ) : Prop :=
  ∀ N : ℕ, ∃ p q : ℕ,
    N < p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q - p ≤ C

/-- The intended public bounded-gaps statement at the new constant 236. -/
def boundedGapsStatement236 : Prop := boundedGapsStatementAt 236

/-- The explicit prime-pair contract for the bound 236. -/
theorem boundedGapsStatement236_contract :
    boundedGapsStatement236 ↔
      ∀ N : ℕ, ∃ p q : ℕ,
        N < p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q - p ≤ 236 := by
  rfl

/-- Arbitrarily large consecutive prime pairs whose difference is at most
`C`. -/
def infinitelyManyBoundedConsecutiveGapsAt (C : ℕ) : Prop :=
  ∀ N : ℕ, ∃ p q : ℕ,
    N < p ∧ BoundedGaps.IsConsecutivePrimePair p q ∧ q - p ≤ C

/-- Passing to the first prime after `p` converts an arbitrary bounded prime
pair into a consecutive bounded prime pair, uniformly in the bound. -/
theorem boundedGapsStatementAt_iff_consecutive (C : ℕ) :
    boundedGapsStatementAt C ↔ infinitelyManyBoundedConsecutiveGapsAt C := by
  constructor
  · intro h N
    obtain ⟨p, q, hNp, hpq, hpp, hqp, hgap⟩ := h N
    let nextPrimeExists : ∃ r : ℕ, p < r ∧ r.Prime := ⟨q, hpq, hqp⟩
    let r := Nat.find nextPrimeExists
    have hr : p < r ∧ r.Prime := Nat.find_spec nextPrimeExists
    have hrq : r ≤ q := Nat.find_min' nextPrimeExists ⟨hpq, hqp⟩
    have hconsecutive : BoundedGaps.IsConsecutivePrimePair p r := by
      refine ⟨hpp, hr.2, hr.1, ?_⟩
      intro s hps hsr hsp
      exact (not_lt_of_ge (Nat.find_min' nextPrimeExists ⟨hps, hsp⟩)) hsr
    exact ⟨p, r, hNp, hconsecutive,
      (Nat.sub_le_sub_right hrq p).trans hgap⟩
  · intro h N
    obtain ⟨p, q, hNp, hpq, hgap⟩ := h N
    exact ⟨p, q, hNp, hpq.2.2.1, hpq.1, hpq.2.1, hgap⟩

/-- The prime-gap liminf statement at a natural bound `C`. -/
def primeGapLiminfStatementAt (C : ℕ) : Prop :=
  Filter.liminf (fun n : ℕ => (BoundedGaps.primeGap n : EReal))
      Filter.atTop ≤ (C : EReal)

/-- The intended liminf formulation at the new constant 236. -/
def primeGapLiminfStatement236 : Prop := primeGapLiminfStatementAt 236

theorem primeGapLiminfStatementAt_infinitelyManyBoundedConsecutiveGapsAt
    {C : ℕ} (h : primeGapLiminfStatementAt C) :
    infinitelyManyBoundedConsecutiveGapsAt C := by
  have hindices :=
    (BoundedGaps.liminf_natCast_le_iff BoundedGaps.primeGap C).mp h
  intro N
  obtain ⟨n, hNn, hgap⟩ := hindices N
  have hNprimeN : N < Nat.nth Nat.Prime N :=
    (show N < N + 2 by omega).trans_le (Nat.add_two_le_nth_prime N)
  have hprimeNn : Nat.nth Nat.Prime N < Nat.nth Nat.Prime n :=
    (Nat.nth_strictMono Nat.infinite_setOf_prime) hNn
  exact ⟨Nat.nth Nat.Prime n, Nat.nth Nat.Prime (n + 1),
    hNprimeN.trans hprimeNn, BoundedGaps.nthPrime_isConsecutivePrimePair n,
    hgap⟩

theorem infinitelyManyBoundedConsecutiveGapsAt_primeGapLiminfStatementAt
    {C : ℕ} (h : infinitelyManyBoundedConsecutiveGapsAt C) :
    primeGapLiminfStatementAt C := by
  apply (BoundedGaps.liminf_natCast_le_iff BoundedGaps.primeGap C).mpr
  intro N
  obtain ⟨p, q, hp_large, hpair, hgap⟩ :=
    h (Nat.nth Nat.Prime (N + 1))
  obtain ⟨hpp, hqp, hpq, hbetween⟩ := hpair
  have hp_range : p ∈ Set.range (Nat.nth Nat.Prime) := by
    rw [Nat.range_nth_of_infinite Nat.infinite_setOf_prime]
    exact hpp
  obtain ⟨m, rfl⟩ := hp_range
  have hq_range : q ∈ Set.range (Nat.nth Nat.Prime) := by
    rw [Nat.range_nth_of_infinite Nat.infinite_setOf_prime]
    exact hqp
  obtain ⟨j, rfl⟩ := hq_range
  have hNm : N < m := by
    have : N + 1 < m :=
      (Nat.nth_lt_nth Nat.infinite_setOf_prime).mp hp_large
    omega
  have hmj : m < j :=
    (Nat.nth_lt_nth Nat.infinite_setOf_prime).mp hpq
  have hj : j = m + 1 := by
    apply Nat.le_antisymm
    · apply Nat.le_of_not_gt
      intro hsuccj
      exact hbetween (Nat.nth Nat.Prime (m + 1))
        ((Nat.nth_strictMono Nat.infinite_setOf_prime) (Nat.lt_succ_self m))
        ((Nat.nth_strictMono Nat.infinite_setOf_prime) hsuccj)
        (Nat.prime_nth_prime (m + 1))
    · omega
  subst j
  exact ⟨m, hNm, by simpa [BoundedGaps.primeGap] using hgap⟩

theorem primeGapLiminfStatementAt_iff_consecutive (C : ℕ) :
    primeGapLiminfStatementAt C ↔ infinitelyManyBoundedConsecutiveGapsAt C := by
  exact ⟨primeGapLiminfStatementAt_infinitelyManyBoundedConsecutiveGapsAt,
    infinitelyManyBoundedConsecutiveGapsAt_primeGapLiminfStatementAt⟩

theorem primeGapLiminfStatementAt_iff_boundedGapsStatementAt (C : ℕ) :
    primeGapLiminfStatementAt C ↔ boundedGapsStatementAt C := by
  rw [primeGapLiminfStatementAt_iff_consecutive,
    ← boundedGapsStatementAt_iff_consecutive]

/-- Equivalence of the explicit prime-pair and prime-gap liminf formulations
at 236. -/
theorem primeGapLiminfStatement236_iff_boundedGapsStatement236 :
    primeGapLiminfStatement236 ↔ boundedGapsStatement236 := by
  exact primeGapLiminfStatementAt_iff_boundedGapsStatementAt 236

end BoundedGaps.H1236

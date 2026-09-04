import PrimeGaps186
import BoundedGaps.H1236.Statement

/-!
# PrimeGaps186 to FormalPantheon H₁ ≤ 236 bridge

This cross-toolchain verification module imports the pinned conditional
`PrimeGaps186` theorem and the actual public FormalPantheon H₁ ≤ 236
statement modules. It is intentionally separate from the Lean 4.32 production
dependency path.
-/

namespace BoundedGaps.H1236

/-- Upstream subtracts after coercing to `EReal`; FormalPantheon subtracts in
`ℕ` and then coerces. The terms agree because the prime enumeration is
monotone. -/
theorem primeGaps186_gapTerm_eq (n : ℕ) :
    (Nat.nth Nat.Prime (n + 1) : EReal) -
        (Nat.nth Nat.Prime n : EReal) =
      (BoundedGaps.primeGap n : EReal) := by
  rw [BoundedGaps.primeGap]
  have hle : Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime (n + 1) :=
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
      (Nat.le_succ n)
  rw [← EReal.coe_coe_eq_natCast, ← EReal.coe_coe_eq_natCast,
    ← EReal.coe_coe_eq_natCast, ← EReal.coe_sub,
    EReal.coe_eq_coe_iff]
  exact (Nat.cast_sub hle).symm

/-- The upstream and FormalPantheon consecutive-prime-gap liminfs are equal. -/
theorem primeGaps186_liminf_eq_formalPantheon :
    PrimeGap186.primeGapLiminf =
      Filter.liminf (fun n : ℕ => (BoundedGaps.primeGap n : EReal))
        Filter.atTop := by
  unfold PrimeGap186.primeGapLiminf
  congr 2
  funext n
  exact primeGaps186_gapTerm_eq n

/-- The pinned upstream theorem gives the FormalPantheon liminf statement at
the stronger bound 186. -/
theorem primeGapLiminfStatement186_of_primeGaps186 :
    primeGapLiminfStatementAt 186 := by
  unfold primeGapLiminfStatementAt
  rw [← primeGaps186_liminf_eq_formalPantheon]
  exact PrimeGap186.primeGapLiminf_le_186

/-- Monotonicity of the numerical bound transfers the upstream result from
186 to the current target 236. -/
theorem primeGapLiminfStatement236_of_primeGaps186 :
    primeGapLiminfStatement236 := by
  unfold primeGapLiminfStatement236 primeGapLiminfStatementAt
  rw [← primeGaps186_liminf_eq_formalPantheon]
  have h186236 : (186 : ℕ) ≤ 236 := by omega
  exact PrimeGap186.primeGapLiminf_le_186.trans
    (EReal.natCast_le_iff.mpr h186236)

/-- The existing FormalPantheon equivalence converts the liminf result into
the public explicit bounded-prime-pair statement. -/
theorem boundedGapsStatement236_of_primeGaps186 :
    boundedGapsStatement236 :=
  primeGapLiminfStatement236_iff_boundedGapsStatement236.mp
    primeGapLiminfStatement236_of_primeGaps186

end BoundedGaps.H1236

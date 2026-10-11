import Analysis.GeneratingFunctions

/-!
Coefficient-level assembly of the inhomogeneous ODE in CDT v2 Proposition
`functionsH`, Section 11.1. The recurrence assumptions are explicit.
-/

namespace DirichletL

set_option maxHeartbeats 800000 in
/-- A homogeneous A/B pair and an inhomogeneous C sequence give the source
right-hand side for a linear combination of their generating series. -/
theorem generatingODE_linearCombination_of_cdtRecurrences
    (aA aB aC : ℕ → ℚ) (α β γ : ℚ)
    (hA0 : aA 1 - 3 * aA 0 = 0)
    (hArec : ∀ n : ℕ, 1 ≤ n →
      (n + 1 : ℚ) ^ 2 * aA (n + 1) -
          (10 * (n : ℚ) * (n + 1 : ℚ) + 3) * aA n +
            9 * (n : ℚ) ^ 2 * aA (n - 1) = 0)
    (hB0 : aB 1 - 3 * aB 0 = 1)
    (hBrec : ∀ n : ℕ, 1 ≤ n →
      (n + 1 : ℚ) ^ 2 * aB (n + 1) -
          (10 * (n : ℚ) * (n + 1 : ℚ) + 3) * aB n +
            9 * (n : ℚ) ^ 2 * aB (n - 1) = 0)
    (hC0 : aC 1 - 3 * aC 0 = 1)
    (hCrec : ∀ n : ℕ, 1 ≤ n →
      (n + 1 : ℚ) ^ 2 * aC (n + 1) -
          (10 * (n : ℚ) * (n + 1 : ℚ) + 3) * aC n +
            9 * (n : ℚ) ^ 2 * aC (n - 1) = 1) :
    generatingODE
        (α • generatingSeries aA + β • generatingSeries aB + γ • generatingSeries aC) =
      generatingSeries (fun n => if n = 0 then β + γ else γ) := by
  let u : ℕ → ℚ := fun n => α * aA n + β * aB n + γ * aC n
  have hseries :
      α • generatingSeries aA + β • generatingSeries aB + γ • generatingSeries aC =
        generatingSeries u := by
    apply PowerSeries.ext
    intro n
    simp [u, generatingSeries, smul_eq_mul, add_assoc, add_left_comm, add_comm]
  rw [hseries]
  apply generatingSeries_ode_eq_of_recurrence u (fun n => if n = 0 then β + γ else γ)
  · dsimp [u]
    linear_combination α * hA0 + β * hB0 + γ * hC0
  · intro n hn
    rw [if_neg (Nat.ne_of_gt hn)]
    have hA := hArec n hn
    have hB := hBrec n hn
    have hC := hCrec n hn
    dsimp [u]
    linear_combination α * hA + β * hB + γ * hC

end DirichletL

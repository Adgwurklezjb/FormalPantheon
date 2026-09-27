import Analysis.SeededAuxiliaryExpression

/-!
The pointwise norm of the literal auxiliary sum, CDT v2 TeX 4130-4150
and 4190-4228, and published UDC equations 2.5.15-2.5.24. Zero factors,
empty sums, and exact exponents are checked before these proofs in

The continuation interface is recorded before this revision in
-/

namespace DirichletL

open scoped Classical Topology

theorem norm_seeded_auxiliary_sum_le {m : ℕ}
    (h D : ℕ) (ε : ℝ) (t : ↥(auxiliaryFreeIndices m h D ε) → ℤ)
    (π : Equiv.Perm (Fin (m * h))) (ψ : Fin (m * h) → ℂ → ℂ)
    (P : Fin m → Fin (m * h) → ℂ → ℂ)
    (H : Polynomial ℂ) (z : Fin (m * h) → ℂ) (S C Γ : ℝ)
    (ht : ∀ v, ‖(t v : ℂ)‖ ≤ Real.exp S)
    (hH : ∀ i j, ‖H.eval (z j) * P i j (z j)‖ ≤ Real.exp C)
    (hweight : ∀ v : ↥(auxiliaryFreeIndices m h D ε),
      ∑ j, ((v.val.2 (π j)).val : ℝ) * Real.log ‖ψ j (z j)‖ ≤ Γ) :
    ‖∑ v, (t v : ℂ) * ∏ j, H.eval (z j) * ψ j (z j) ^ (v.val.2 (π j)).val *
      P (v.val.1 (π j)) j (z j)‖ ≤
        Real.exp (Real.log ((auxiliaryFreeIndices m h D ε).card : ℝ) +
          S + (m * h : ℕ) * C + Γ) := by
  have hfactor (v : ↥(auxiliaryFreeIndices m h D ε)) (j : Fin (m * h)) :
      ‖H.eval (z j) * ψ j (z j) ^ (v.val.2 (π j)).val *
        P (v.val.1 (π j)) j (z j)‖ ≤
          Real.exp (C + ((v.val.2 (π j)).val : ℝ) * Real.log ‖ψ j (z j)‖) := by
    have hp : ‖ψ j (z j)‖ ^ (v.val.2 (π j)).val ≤
        Real.exp (((v.val.2 (π j)).val : ℝ) * Real.log ‖ψ j (z j)‖) := by
      simpa only [Real.exp_nat_mul] using
        pow_le_pow_left₀ (norm_nonneg _) (Real.le_exp_log ‖ψ j (z j)‖) (v.val.2 (π j)).val
    calc
      ‖H.eval (z j) * ψ j (z j) ^ (v.val.2 (π j)).val *
          P (v.val.1 (π j)) j (z j)‖ =
          ‖(H.eval (z j) * P (v.val.1 (π j)) j (z j)) *
            ψ j (z j) ^ (v.val.2 (π j)).val‖ := congrArg norm (mul_right_comm _ _ _)
      _ ≤ Real.exp C *
          Real.exp (((v.val.2 (π j)).val : ℝ) * Real.log ‖ψ j (z j)‖) := by
        rw [norm_mul, norm_pow]
        exact mul_le_mul (hH _ j) hp (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have hproduct (v : ↥(auxiliaryFreeIndices m h D ε)) :
      ‖∏ j, H.eval (z j) * ψ j (z j) ^ (v.val.2 (π j)).val *
        P (v.val.1 (π j)) j (z j)‖ ≤
          Real.exp ((m * h : ℕ) * C +
            ∑ j, ((v.val.2 (π j)).val : ℝ) * Real.log ‖ψ j (z j)‖) := by
    calc
      _ ≤ ∏ j, Real.exp (C + ((v.val.2 (π j)).val : ℝ) * Real.log ‖ψ j (z j)‖) := by
        rw [norm_prod]
        exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => hfactor v j)
      _ = _ := by
        rw [← Real.exp_sum, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hterm (v : ↥(auxiliaryFreeIndices m h D ε)) :
      ‖(t v : ℂ) * ∏ j, H.eval (z j) * ψ j (z j) ^ (v.val.2 (π j)).val *
        P (v.val.1 (π j)) j (z j)‖ ≤ Real.exp (S + (m * h : ℕ) * C + Γ) := by
    calc
      _ ≤ Real.exp S * Real.exp ((m * h : ℕ) * C +
          ∑ j, ((v.val.2 (π j)).val : ℝ) * Real.log ‖ψ j (z j)‖) := by
        rw [norm_mul]
        exact mul_le_mul (ht v) (hproduct v) (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (S + (m * h : ℕ) * C +
          ∑ j, ((v.val.2 (π j)).val : ℝ) * Real.log ‖ψ j (z j)‖) := by
        rw [← Real.exp_add, add_assoc]
      _ ≤ _ := Real.exp_le_exp.mpr (add_le_add_left (hweight v) _)
  calc
    _ ≤ ∑ v, ‖(t v : ℂ) * ∏ j, H.eval (z j) * ψ j (z j) ^ (v.val.2 (π j)).val *
        P (v.val.1 (π j)) j (z j)‖ := norm_sum_le _ _
    _ ≤ ∑ _v : ↥(auxiliaryFreeIndices m h D ε), Real.exp (S + (m * h : ℕ) * C + Γ) :=
      Finset.sum_le_sum (fun v _ => hterm v)
    _ = ((auxiliaryFreeIndices m h D ε).card : ℝ) *
        Real.exp (S + (m * h : ℕ) * C + Γ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ Real.exp (Real.log ((auxiliaryFreeIndices m h D ε).card : ℝ)) *
        Real.exp (S + (m * h : ℕ) * C + Γ) :=
      mul_le_mul_of_nonneg_right (Real.le_exp_log _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem norm_seeded_auxiliary_sum_le_of_log_bound {m : ℕ}
    (h D : ℕ) (ε : ℝ) (t : ↥(auxiliaryFreeIndices m h D ε) → ℤ)
    (π : Equiv.Perm (Fin (m * h))) (ψ : Fin (m * h) → ℂ → ℂ)
    (P : Fin m → Fin (m * h) → ℂ → ℂ)
    (H : Polynomial ℂ) (z : Fin (m * h) → ℂ) (S C L : ℝ) (hL : 0 ≤ L)
    (ht : ∀ v, ‖(t v : ℂ)‖ ≤ Real.exp S)
    (hH : ∀ i j, ‖H.eval (z j) * P i j (z j)‖ ≤ Real.exp C)
    (hlog : ∀ j, Real.log ‖ψ j (z j)‖ ≤ L) :
    ‖∑ v, (t v : ℂ) * ∏ j, H.eval (z j) * ψ j (z j) ^ (v.val.2 (π j)).val *
      P (v.val.1 (π j)) j (z j)‖ ≤
        Real.exp (Real.log ((auxiliaryFreeIndices m h D ε).card : ℝ) +
          S + (m * h : ℕ) * C + (m * h : ℕ) * (D : ℝ) * L) := by
  apply norm_seeded_auxiliary_sum_le h D ε t π ψ P H z S C _ ht hH
  intro v
  calc
    _ ≤ ∑ _j : Fin (m * h), (D : ℝ) * L := by
      apply Finset.sum_le_sum
      intro j _
      exact (mul_le_mul_of_nonneg_left (hlog j) (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast (v.val.2 (π j)).isLt.le) hL)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_assoc]

end DirichletL

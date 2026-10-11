import Analysis.BlockVandermondePolynomial
import Analysis.VandermondeUnitBound

/-!
The block-product bounds in CDT v2, supplied TeX 4069-4092, and published
UDC Sections 2.5.14-2.5.20. The sufficient universal bound and strict
positive-power case precede these proofs in
-/

namespace DirichletL

theorem sum_card_block_fibers {d : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : Fin d → κ) :
    ∑ k, (Finset.univ.filter (fun i => b i = k)).card = d := by
  simpa only [Finset.card_univ, Fintype.card_fin] using
    (Finset.card_eq_sum_card_fiberwise (f := b) (s := Finset.univ)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)).symm

theorem norm_eval_blockVandermondePolynomial_le {d : ℕ} {κ : Type*}
    [Fintype κ] [DecidableEq κ] (b : Fin d → κ) (M : ℕ) (hd : 0 < d)
    (z : Fin d → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    ‖MvPolynomial.eval z (blockVandermondePolynomial b M)‖ ≤
      Real.exp ((M : ℝ) * (d : ℝ) * Real.log (d : ℝ)) := by
  let S (k : κ) := Finset.univ.filter (fun i => b i = k)
  let V (k : κ) := (Matrix.vandermonde (fun i => z ((S k).orderEmbOfFin rfl i))).det
  have hsum : ∑ k, ((S k).card : ℝ) = (d : ℝ) := by
    exact_mod_cast sum_card_block_fibers b
  have hV (k : κ) : ‖V k‖ ≤ Real.exp (((S k).card : ℝ) * Real.log (d : ℝ)) :=
    norm_vandermonde_le_exp hd (by simpa using Finset.card_le_univ (S k))
      (fun i => z ((S k).orderEmbOfFin rfl i)) (fun i => hz _)
  rw [eval_blockVandermondePolynomial, norm_prod]
  change (∏ k, ‖V k ^ M‖) ≤ _
  calc
    (∏ k, ‖V k ^ M‖) ≤
        ∏ k, Real.exp ((M : ℝ) * ((S k).card : ℝ) * Real.log (d : ℝ)) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro k _
      rw [norm_pow]
      calc
        ‖V k‖ ^ M ≤ (Real.exp (((S k).card : ℝ) * Real.log (d : ℝ))) ^ M :=
          pow_le_pow_left₀ (norm_nonneg _) (hV k) M
        _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ = Real.exp ((M : ℝ) * (d : ℝ) * Real.log (d : ℝ)) := by
      rw [← Real.exp_sum]
      congr 1
      rw [← Finset.sum_mul, ← Finset.mul_sum, hsum]

theorem norm_eval_blockVandermondePolynomial_lt_of_block {d : ℕ} {κ : Type*}
    [Fintype κ] [DecidableEq κ] (b : Fin d → κ) (M : ℕ) (hM : 0 < M)
    (hd : 0 < d) (z : Fin d → ℂ) (hz : ∀ i, ‖z i‖ = 1) (k : κ) (B : ℝ)
    (hB : ‖(Matrix.vandermonde (fun i => z
      ((Finset.univ.filter (fun j => b j = k)).orderEmbOfFin rfl i))).det‖ < Real.exp B) :
    ‖MvPolynomial.eval z (blockVandermondePolynomial b M)‖ <
      Real.exp ((M : ℝ) * (B + (d : ℝ) * Real.log (d : ℝ))) := by
  let S (j : κ) := Finset.univ.filter (fun i => b i = j)
  let V (j : κ) := (Matrix.vandermonde (fun i => z ((S j).orderEmbOfFin rfl i))).det
  have hsum : ∑ j, ((S j).card : ℝ) = (d : ℝ) := by
    exact_mod_cast sum_card_block_fibers b
  have hlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hrest : (∏ j ∈ Finset.univ.erase k, ‖V j‖) ≤
      Real.exp ((d : ℝ) * Real.log (d : ℝ)) := by
    calc
      (∏ j ∈ Finset.univ.erase k, ‖V j‖) ≤
          ∏ j ∈ Finset.univ.erase k,
            Real.exp (((S j).card : ℝ) * Real.log (d : ℝ)) := by
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro j _
        exact norm_vandermonde_le_exp hd (by simpa using Finset.card_le_univ (S j))
          (fun i => z ((S j).orderEmbOfFin rfl i)) (fun i => hz _)
      _ ≤ Real.exp ((d : ℝ) * Real.log (d : ℝ)) := by
        rw [← Real.exp_sum]
        apply Real.exp_le_exp.mpr
        rw [← Finset.sum_mul]
        apply mul_le_mul_of_nonneg_right _ hlog
        exact (Finset.sum_le_univ_sum_of_nonneg
          (fun j => show (0 : ℝ) ≤ ((S j).card : ℝ) from Nat.cast_nonneg _)).trans_eq hsum
  have hprod : ‖∏ j, V j‖ < Real.exp (B + (d : ℝ) * Real.log (d : ℝ)) := by
    rw [norm_prod, ← Finset.mul_prod_erase Finset.univ (fun j => ‖V j‖)
      (Finset.mem_univ k), Real.exp_add]
    exact (mul_le_mul_of_nonneg_left hrest (norm_nonneg (V k))).trans_lt
      (mul_lt_mul_of_pos_right hB (Real.exp_pos _))
  rw [eval_blockVandermondePolynomial, Finset.prod_pow, norm_pow]
  change ‖∏ j, V j‖ ^ M < _
  calc
    ‖∏ j, V j‖ ^ M < (Real.exp (B + (d : ℝ) * Real.log (d : ℝ))) ^ M :=
      pow_lt_pow_left₀ hprod (norm_nonneg _) (Nat.ne_of_gt hM)
    _ = _ := by rw [Real.exp_nat_mul]

end DirichletL

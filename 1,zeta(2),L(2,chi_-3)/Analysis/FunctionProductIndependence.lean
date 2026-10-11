import Comparator.Statement

/-!
Finite independence for the products in CDT v2, supplied TeX
2910-2935 and 3965-3998. The zero estimate is a separate obligation.
-/

namespace DirichletL

open scoped Classical

theorem linearIndependent_external_product {K ι κ α β : Type*} [Field K]
    [Fintype ι] [Fintype κ] {f : ι → α → K} {g : κ → β → K}
    (hf : LinearIndependent K f) (hg : LinearIndependent K g) :
    LinearIndependent K (fun p : ι × κ =>
      fun q : α × β => f p.1 q.1 * g p.2 q.2) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc p
  have hcol (x : α) (j : κ) : ∑ i, c (i, j) * f i x = 0 := by
    apply Fintype.linearIndependent_iff.mp hg (fun j => ∑ i, c (i, j) * f i x) ?_ j
    funext y
    have hxy := congrFun hc (x, y)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Fintype.sum_prod_type] at hxy ⊢
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simpa only [mul_assoc] using hxy
  have hrow : ∑ i, c (i, p.2) • f i = 0 := by
    funext x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      using hcol x p.2
  exact Fintype.linearIndependent_iff.mp hf _ hrow p.1

theorem linearIndependent_fin_product {K ι α : Type*} [Field K] [Fintype ι]
    {f : ι → α → K} (hf : LinearIndependent K f) (d : ℕ) :
    LinearIndependent K (fun σ : Fin d → ι =>
      fun n : Fin d → α => ∏ j, f (σ j) (n j)) := by
  induction d with
  | zero =>
    apply linearIndependent_unique _
    intro h
    have hzero := congrFun h (fun i : Fin 0 => Fin.elim0 i)
    simp at hzero
  | succ d ih =>
    have hprod := linearIndependent_external_product hf ih
    let e := Fin.consEquiv (fun _ : Fin (d + 1) => ι)
    apply Fintype.linearIndependent_iff.mpr
    intro c hc σ
    have hz : ∑ p : ι × (Fin d → ι), c (e p) •
        (fun q : α × (Fin d → α) => f p.1 q.1 * ∏ j, f (p.2 j) (q.2 j)) = 0 := by
      funext q
      have hq := congrFun hc (Fin.cons q.1 q.2)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hq ⊢
      rw [← e.sum_comp] at hq
      simpa only [e, Fin.consEquiv, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
        using hq
    have hσ := Fintype.linearIndependent_iff.mp hprod _ hz (σ 0, Fin.tail σ)
    change c (Fin.cons (σ 0) (Fin.tail σ)) = 0 at hσ
    simpa only [Fin.cons_self_tail] using hσ

end DirichletL

import Comparator.Statement

/-!
The central multinomial maximum in CDT v2, supplied TeX 3806-3823.
A transfer from a larger count to a smaller count strictly decreases
the factorial product until the integer-mean profile is constant.
-/

namespace DirichletL

open scoped Nat

theorem factorial_transfer_lt {a b : ℕ} (h : b + 1 < a) :
    (a - 1)! * (b + 1)! < a ! * b ! := by
  have ha : a ≠ 0 := by omega
  calc
    _ = (b + 1) * ((a - 1)! * b !) := by rw [Nat.factorial_succ]; ring
    _ < a * ((a - 1)! * b !) := Nat.mul_lt_mul_of_pos_right h
      (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
    _ = _ := by rw [← mul_assoc, Nat.mul_factorial_pred ha]

theorem sum_update_transfer {m : ℕ} (f : Fin m → ℕ) (i j : Fin m)
    (hij : i ≠ j) (hi : 0 < f i) :
    (∑ k : Fin m, Function.update (Function.update f i (f i - 1)) j (f j + 1) k) =
      ∑ k : Fin m, f k := by
  let g : Fin m → ℕ := Function.update f i (f i - 1)
  have h₁ := Finset.sum_update_of_mem (Finset.mem_univ i) f (f i - 1)
  have h₂ := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)
  have h₃ := Finset.sum_update_of_mem (Finset.mem_univ j) g (f j + 1)
  have h₄ := Finset.add_sum_erase Finset.univ g (Finset.mem_univ j)
  simp only [Finset.sdiff_singleton_eq_erase] at h₁ h₃
  change (∑ k : Fin m, g k) = f i - 1 + ∑ k ∈ Finset.univ.erase i, f k at h₁
  have hgj : g j = f j := by simp [g, hij.symm]
  rw [hgj] at h₄
  change (∑ k : Fin m, Function.update g j (f j + 1) k) = ∑ k : Fin m, f k
  omega

theorem prod_factorial_update_transfer_lt {m : ℕ} (f : Fin m → ℕ) (i j : Fin m)
    (hgap : f j + 1 < f i) :
    (∏ k : Fin m, (Function.update (Function.update f i (f i - 1)) j (f j + 1) k)!) <
      ∏ k : Fin m, (f k)! := by
  have hij : i ≠ j := by intro h; subst j; omega
  let s : Finset (Fin m) := (Finset.univ.erase i).erase j
  let u : Fin m → ℕ := Function.update (Function.update f i (f i - 1)) j (f j + 1)
  have hprod (g : Fin m → ℕ) :
      (∏ k : Fin m, (g k)!) = (g i)! * (g j)! * ∏ k ∈ s, (g k)! := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k : Fin m => (g k)!) (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) (fun k : Fin m => (g k)!)
        (by simp [hij.symm] : j ∈ Finset.univ.erase i)]
    dsimp only [s]
    ring
  have hui : u i = f i - 1 := by simp [u, hij]
  have huj : u j = f j + 1 := by simp [u]
  have hrest : (∏ k ∈ s, (u k)!) = ∏ k ∈ s, (f k)! := by
    apply Finset.prod_congr rfl
    intro k hk
    dsimp only [s] at hk
    obtain ⟨hkj, hki⟩ := Finset.mem_erase.mp hk
    have hkni := (Finset.mem_erase.mp hki).1
    simp [u, hkj, hkni]
  change (∏ k : Fin m, (u k)!) < ∏ k : Fin m, (f k)!
  rw [hprod u, hprod f, hui, huj, hrest]
  exact Nat.mul_lt_mul_of_pos_right (factorial_transfer_lt hgap) (Nat.prod_factorial_pos s f)

theorem prod_factorial_const_le_of_sum_eq {m h : ℕ} (f : Fin m → ℕ)
    (hf : (∑ i : Fin m, f i) = m * h) : (h !) ^ m ≤ ∏ i : Fin m, (f i)! := by
  classical
  have hnonempty : (Finset.finAntidiagonal m (m * h)).Nonempty := by
    refine ⟨fun _ => h, ?_⟩
    simp only [Finset.mem_finAntidiagonal, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  obtain ⟨g, hg, hmin⟩ := Finset.exists_min_image (Finset.finAntidiagonal m (m * h))
    (fun g : Fin m → ℕ => ∏ i : Fin m, (g i)!) hnonempty
  have hsum : (∑ i : Fin m, g i) = m * h := Finset.mem_finAntidiagonal.mp hg
  have heq : ∀ i : Fin m, g i = h := by
    by_contra hnot
    have habove : ∃ i : Fin m, h < g i := by
      by_contra hnone
      push_neg at hnone
      have hsum' : (∑ i : Fin m, g i) = ∑ i : Fin m, h := by simpa using hsum
      have hall := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
        (f := g) (g := fun _ => h) (fun i _ => hnone i)).mp hsum'
      exact hnot (fun i => hall i (Finset.mem_univ i))
    have hbelow : ∃ j : Fin m, g j < h := by
      by_contra hnone
      push_neg at hnone
      have hsum' : (∑ i : Fin m, h) = ∑ i : Fin m, g i := by simpa using hsum.symm
      have hall := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
        (f := fun _ => h) (g := g) (fun i _ => hnone i)).mp hsum'
      exact hnot (fun i => (hall i (Finset.mem_univ i)).symm)
    obtain ⟨i, hi⟩ := habove
    obtain ⟨j, hj⟩ := hbelow
    have hij : i ≠ j := by intro h; subst j; omega
    let g' : Fin m → ℕ := Function.update (Function.update g i (g i - 1)) j (g j + 1)
    have hnew : g' ∈ Finset.finAntidiagonal m (m * h) := by
      apply Finset.mem_finAntidiagonal.mpr
      exact (sum_update_transfer g i j hij (by omega)).trans hsum
    have hle := hmin g' hnew
    have hlt := prod_factorial_update_transfer_lt g i j (by omega)
    exact (not_lt_of_ge hle) hlt
  calc
    _ = ∏ i : Fin m, (g i)! := by simp [heq]
    _ ≤ ∏ i : Fin m, (f i)! := hmin f (Finset.mem_finAntidiagonal.mpr hf)

theorem multinomial_le_const_of_sum_eq {m h : ℕ} (f : Fin m → ℕ)
    (hf : (∑ i : Fin m, f i) = m * h) :
    Nat.multinomial Finset.univ f ≤ Nat.multinomial Finset.univ (fun _ : Fin m => h) := by
  unfold Nat.multinomial
  rw [hf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_id, Finset.prod_const]
  exact Nat.div_le_div_left (prod_factorial_const_le_of_sum_eq f hf) (pow_pos (Nat.factorial_pos h) m)

end DirichletL

import Analysis.QPochhammerSummation

/-!
Jacobi's triple product in integer formal power series, specialized to
arbitrary factors `a * b = X^d`, with `d > 0`. See Lau-Lee-Ono v3, Theorem 4.1.4.
This supplies the theta/product bridge needed for CDT v2 Section 11.1;
the level-six modular identifications are separate obligations.
-/

namespace DirichletL

open scoped PowerSeries.WithPiTopology

private def natPairDiagonalEquiv : (ℕ × ℕ) ⊕ (ℕ × ℕ) ≃ ℕ × ℕ where
  toFun := Sum.elim (fun p => (p.2 + p.1, p.2)) (fun p => (p.2, p.2 + p.1 + 1))
  invFun p := if p.2 ≤ p.1 then Sum.inl (p.1 - p.2, p.2)
    else Sum.inr (p.2 - p.1 - 1, p.1)
  left_inv := by
    intro s
    cases s with
    | inl p =>
      rcases p with ⟨l, k⟩
      simp [show k ≤ k + l by omega]
    | inr p =>
      rcases p with ⟨l, k⟩
      have h : ¬k + l + 1 ≤ k := by omega
      simp [h]
      omega
  right_inv := by
    rintro ⟨i, j⟩
    dsimp
    split_ifs <;> apply Prod.ext <;> dsimp <;> omega

private theorem choose_two_diagonal (k l : ℕ) :
    (k + l).choose 2 + k.choose 2 + k = l.choose 2 + k * (k + l) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : (k + l + 1).choose 2 = k + l + (k + l).choose 2 := by
      simpa using Nat.choose_succ_succ (k + l) 1
    have h2 : (k + 1).choose 2 = k + k.choose 2 := by
      simpa using Nat.choose_succ_succ k 1
    rw [show k + 1 + l = k + l + 1 by omega, h1, h2]
    nlinarith

private theorem qEulerTerm_mul_diagonal {d : ℕ} {a b : PowerSeries ℤ}
    (hab : a * b = PowerSeries.X ^ d) (l k : ℕ) :
    qEulerTerm a d (k + l) * qEulerTerm b d k =
      ((-a) ^ l * (PowerSeries.X ^ d) ^ l.choose 2) * qDurfeeTerm d l k := by
  let q : PowerSeries ℤ := PowerSeries.X ^ d
  have hp : (-a) ^ (k + l) * (-b) ^ k * q ^ ((k + l).choose 2 + k.choose 2) =
      (-a) ^ l * q ^ (l.choose 2 + k * (k + l)) := by
    calc
      _ = (-a) ^ l * ((-a) * (-b)) ^ k * q ^ ((k + l).choose 2 + k.choose 2) := by
        rw [mul_pow, pow_add]
        ring
      _ = (-a) ^ l * q ^ (k + ((k + l).choose 2 + k.choose 2)) := by
        rw [neg_mul_neg, hab]
        simp only [q, pow_add]
        ring
      _ = _ := by
        have he := choose_two_diagonal k l
        have he' : k + ((k + l).choose 2 + k.choose 2) = l.choose 2 + k * (k + l) := by omega
        rw [he']
  dsimp [qEulerTerm, qDurfeeTerm]
  change qPochhammerInvSeries d (k + l) * (-a) ^ (k + l) * q ^ (k + l).choose 2 *
      (qPochhammerInvSeries d k * (-b) ^ k * q ^ k.choose 2) = _
  calc
    _ = (qPochhammerInvSeries d k * qPochhammerInvSeries d (k + l)) *
        ((-a) ^ (k + l) * (-b) ^ k * q ^ ((k + l).choose 2 + k.choose 2)) := by
          rw [pow_add]
          ring
    _ = (qPochhammerInvSeries d k * qPochhammerInvSeries d (k + l)) *
        ((-a) ^ l * q ^ (l.choose 2 + k * (k + l))) := by rw [hp]
    _ = _ := by rw [pow_add]; ring

/-- Jacobi's bilateral sum, split into nonnegative and strictly negative indices. -/
theorem jacobiTripleProduct {d : ℕ} {a b : PowerSeries ℤ}
    (hd : 0 < d) (hab : a * b = PowerSeries.X ^ d) :
    formalProduct (fun i => 1 - (PowerSeries.X ^ d) ^ (i + 1)) *
      formalProduct (fun i => 1 - a * (PowerSeries.X ^ d) ^ i) *
      formalProduct (fun i => 1 - b * (PowerSeries.X ^ d) ^ i) =
        (∑' n : ℕ, (-a) ^ n * (PowerSeries.X ^ d) ^ n.choose 2) +
        (∑' n : ℕ, (-b) ^ (n + 1) * (PowerSeries.X ^ d) ^ (n + 1).choose 2) := by
  let P : PowerSeries ℤ := formalProduct (fun i => 1 - (PowerSeries.X ^ d) ^ (i + 1))
  let A := formalProduct (fun i => 1 - a * (PowerSeries.X ^ d) ^ i)
  let B := formalProduct (fun i => 1 - b * (PowerSeries.X ^ d) ^ i)
  let I := formalProduct (fun i => oneSubInv (d * (i + 1)))
  let t (c : PowerSeries ℤ) (n : ℕ) := (-c) ^ n * (PowerSeries.X ^ d) ^ n.choose 2
  let F (p : ℕ × ℕ) := qEulerTerm a d p.1 * qEulerTerm b d p.2
  let e := natPairDiagonalEquiv
  let F1 (p : ℕ × ℕ) := F (e (Sum.inl p))
  let F2 (p : ℕ × ℕ) := F (e (Sum.inr p))
  have hbound (m k : ℕ) (hk : m + 2 ≤ k) : m < d * k.choose 2 := by
    have h1 := le_choose_two_add_one k
    have h2 := Nat.mul_le_mul_right (k.choose 2) (show 1 ≤ d by omega)
    omega
  have hF : Summable F := by
    apply summable_powerSeries_of_finite_coeff F
      (fun m => (Finset.range (m + 2)) ×ˢ (Finset.range (m + 2)))
    intro m p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    by_cases hi : p.1 < m + 2
    · exact PowerSeries.X_pow_dvd_iff.mp
        (dvd_mul_of_dvd_right (X_pow_dvd_qEulerTerm b d p.2) (qEulerTerm a d p.1))
        m (hbound m p.2 (by omega))
    · exact PowerSeries.X_pow_dvd_iff.mp
        (dvd_mul_of_dvd_left (X_pow_dvd_qEulerTerm a d p.1) (qEulerTerm b d p.2))
        m (hbound m p.1 (by omega))
  have hprod : A * B = ∑' p, F p :=
    ((hasSum_qEulerTerm hd).mul (hasSum_qEulerTerm hd) hF).tsum_eq.symm
  have hs : Summable (fun s => F (e s)) := hF.comp_injective e.injective
  have h1 : Summable F1 := hs.comp_injective Sum.inl_injective
  have h2 : Summable F2 := hs.comp_injective Sum.inr_injective
  have ht (c : PowerSeries ℤ) : Summable (t c) := by
    apply summable_powerSeries_of_finite_coeff (t c) (fun m => Finset.range (m + 2))
    intro m k hk
    have hq : (PowerSeries.X : PowerSeries ℤ) ^ (d * k.choose 2) ∣
        (PowerSeries.X ^ d) ^ k.choose 2 := by rw [← pow_mul]
    exact PowerSeries.X_pow_dvd_iff.mp (dvd_mul_of_dvd_right hq ((-c) ^ k))
      m (hbound m k (by simpa only [Finset.mem_range, not_lt] using hk))
  have hleft (l : ℕ) : (∑' k, F1 (l, k)) = t a l * I := by
    change (∑' k, qEulerTerm a d (k + l) * qEulerTerm b d k) = _
    simp_rw [qEulerTerm_mul_diagonal hab]
    exact ((hasSum_qDurfeeTerm hd l).mul_left (t a l)).tsum_eq
  have hab' : b * a = PowerSeries.X ^ d := by rw [mul_comm]; exact hab
  have hright (l : ℕ) : (∑' k, F2 (l, k)) = t b (l + 1) * I := by
    change (∑' k, qEulerTerm a d k * qEulerTerm b d (k + l + 1)) = _
    have hterm (k : ℕ) : qEulerTerm a d k * qEulerTerm b d (k + l + 1) =
        t b (l + 1) * qDurfeeTerm d (l + 1) k := by
      rw [mul_comm]
      simpa only [Nat.add_assoc, t] using qEulerTerm_mul_diagonal hab' (l + 1) k
    simp_rw [hterm]
    exact ((hasSum_qDurfeeTerm hd (l + 1)).mul_left (t b (l + 1))).tsum_eq
  have hAB : A * B = ((∑' n, t a n) + (∑' n, t b (n + 1))) * I := by
    calc
      _ = ∑' p, F p := hprod
      _ = ∑' s, F (e s) := (e.tsum_eq F).symm
      _ = (∑' p, F1 p) + (∑' p, F2 p) :=
        Summable.tsum_sum (f := fun s => F (e s)) h1 h2
      _ = (∑' l, ∑' k, F1 (l, k)) + (∑' l, ∑' k, F2 (l, k)) := by
        rw [h1.tsum_prod, h2.tsum_prod]
      _ = (∑' l, t a l * I) + (∑' l, t b (l + 1) * I) := by simp_rw [hleft, hright]
      _ = (∑' l, t a l) * I + (∑' l, t b (l + 1)) * I := by
        apply congrArg₂ (· + ·) ((ht a).tsum_mul_right I)
        simpa only [Function.comp_apply, Nat.succ_eq_add_one] using
          ((ht b).comp_injective Nat.succ_injective).tsum_mul_right I
      _ = _ := by ring
  have hPI : P * I = 1 := formalProduct_qPochhammer_mul_inv hd
  change P * A * B = (∑' n, t a n) + (∑' n, t b (n + 1))
  calc
    _ = P * (A * B) := mul_assoc _ _ _
    _ = P * (((∑' n, t a n) + (∑' n, t b (n + 1))) * I) := by rw [hAB]
    _ = (P * I) * ((∑' n, t a n) + (∑' n, t b (n + 1))) := by ring
    _ = _ := by rw [hPI, one_mul]

end DirichletL

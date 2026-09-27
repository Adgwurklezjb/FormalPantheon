import Arithmetic.PowerSeriesEuler

/-!
Polynomial derivative rows for the regular-system specialization of CDT v2
`lem_Shidlovsky`, supplied TeX 2910-2935. Meanings, native interfaces, and
-/

noncomputable section

namespace DirichletL

open scoped Matrix

/-- The Euler derivation X*d/dX on polynomials. -/
def polynomialEuler (R : Type*) [CommRing R] :
    Derivation R (Polynomial R) (Polynomial R) :=
  (Polynomial.X : Polynomial R) • Polynomial.derivative'

theorem polynomialEuler_apply {R : Type*} [CommRing R] (p : Polynomial R) :
    polynomialEuler R p = Polynomial.X * p.derivative := rfl

theorem natDegree_polynomialEuler_le {R : Type*} [CommRing R] (p : Polynomial R) :
    (polynomialEuler R p).natDegree ≤ p.natDegree := by
  rw [polynomialEuler_apply]
  by_cases hp : p.natDegree = 0
  · rw [Polynomial.derivative_of_natDegree_zero hp, mul_zero, Polynomial.natDegree_zero]
    exact Nat.zero_le _
  · have h := Polynomial.natDegree_mul_le (p := Polynomial.X) (q := p.derivative)
    have hX := Polynomial.natDegree_X_le (R := R)
    have hd := Polynomial.natDegree_derivative_le p
    omega

theorem coe_polynomialEuler {R : Type*} [CommRing R] (p : Polynomial R) :
    (polynomialEuler R p : PowerSeries R) = powerSeriesEuler R (p : PowerSeries R) := by
  rw [polynomialEuler_apply, Polynomial.coe_mul, Polynomial.coe_X, powerSeriesEuler_apply,
    PowerSeries.derivativeFun_coe]

/-- Polynomial rows representing successive Euler derivatives after clearing powers of q. -/
def polynomialEulerRows {σ R : Type*} [Fintype σ] [CommRing R]
    (q : Polynomial R) (C : Matrix σ σ (Polynomial R)) (P : σ → Polynomial R) :
    ℕ → σ → Polynomial R
  | 0 => P
  | n + 1 => fun j => q * polynomialEuler R (polynomialEulerRows q C P n j) +
      (polynomialEulerRows q C P n ᵥ* C) j -
        (n : Polynomial R) * polynomialEuler R q * polynomialEulerRows q C P n j

theorem polynomialEulerRows_zero {σ R : Type*} [Fintype σ] [CommRing R]
    (q : Polynomial R) (C : Matrix σ σ (Polynomial R)) (P : σ → Polynomial R) :
    polynomialEulerRows q C P 0 = P := rfl

theorem polynomialEulerRows_succ {σ R : Type*} [Fintype σ] [CommRing R]
    (q : Polynomial R) (C : Matrix σ σ (Polynomial R)) (P : σ → Polynomial R)
    (n : ℕ) (j : σ) :
    polynomialEulerRows q C P (n + 1) j = q * polynomialEuler R (polynomialEulerRows q C P n j) +
      (polynomialEulerRows q C P n ᵥ* C) j -
        (n : Polynomial R) * polynomialEuler R q * polynomialEulerRows q C P n j := rfl

theorem polynomialEulerRows_natDegree_le {σ R : Type*} [Fintype σ] [CommRing R]
    (q : Polynomial R) (C : Matrix σ σ (Polynomial R)) (P : σ → Polynomial R)
    (E d : ℕ) (hP : ∀ j, (P j).natDegree ≤ E) (hq : q.natDegree ≤ d)
    (hC : ∀ i j, (C i j).natDegree ≤ d) (n : ℕ) (j : σ) :
    (polynomialEulerRows q C P n j).natDegree ≤ E + n * d := by
  classical
  induction n generalizing j with
  | zero => simpa only [polynomialEulerRows_zero, Nat.zero_mul, Nat.add_zero] using hP j
  | succ n ih =>
    rw [polynomialEulerRows_succ]
    have hj := ih j
    have hnd : (n + 1) * d = n * d + d := Nat.succ_mul n d
    have h₁ : (q * polynomialEuler R (polynomialEulerRows q C P n j)).natDegree ≤
        E + (n + 1) * d := by
      have h := Polynomial.natDegree_mul_le (p := q)
        (q := polynomialEuler R (polynomialEulerRows q C P n j))
      have he := natDegree_polynomialEuler_le (polynomialEulerRows q C P n j)
      omega
    have h₂ : ((polynomialEulerRows q C P n ᵥ* C) j).natDegree ≤ E + (n + 1) * d := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i _
      change (polynomialEulerRows q C P n i * C i j).natDegree ≤ E + (n + 1) * d
      have hi := ih i
      have h := Polynomial.natDegree_mul_le (p := polynomialEulerRows q C P n i) (q := C i j)
      have hc := hC i j
      omega
    have h₃ : ((n : Polynomial R) * polynomialEuler R q *
        polynomialEulerRows q C P n j).natDegree ≤ E + (n + 1) * d := by
      have h := Polynomial.natDegree_mul_le (p := (n : Polynomial R) * polynomialEuler R q)
        (q := polynomialEulerRows q C P n j)
      have hn := Polynomial.natDegree_mul_le (p := (n : Polynomial R)) (q := polynomialEuler R q)
      rw [Polynomial.natDegree_natCast] at hn
      have he := natDegree_polynomialEuler_le q
      omega
    simpa only [max_self] using Polynomial.natDegree_sub_le_of_le
      (Polynomial.natDegree_add_le_of_degree_le h₁ h₂) h₃

end DirichletL

import Mathlib

/-!
Regrouping an absolutely convergent positive double series by the product
of its indices, as needed in CDT v2 Section 11.1's q-series identities.
The proof follows Mathlib's L-series convolution regrouping API.
-/

namespace DirichletL

/-- Adding the two zero axes preserves the sum of a positive double series. -/
theorem hasSum_natProd_succ_iff {E : Type*} [NormedAddCommGroup E]
    {f : ℕ → ℕ → E} {a : E}
    (hleft : ∀ n, f 0 n = 0) (hright : ∀ n, f n 0 = 0) :
    HasSum (fun p : ℕ × ℕ => f (p.1 + 1) (p.2 + 1)) a ↔
      HasSum (fun p : ℕ × ℕ => f p.1 p.2) a := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (p.1 + 1, p.2 + 1)) := by
    intro p r h
    exact Prod.ext (by simpa using congrArg Prod.fst h)
      (by simpa using congrArg Prod.snd h)
  refine hinj.hasSum_iff (f := fun p : ℕ × ℕ => f p.1 p.2) ?_
  rintro ⟨n, k⟩ hnot
  by_cases hn : n = 0
  · simpa [hn] using hleft k
  by_cases hk : k = 0
  · simpa [hk] using hright n
  exact (hnot ⟨(n - 1, k - 1), by
    simp [Nat.sub_add_cancel (Nat.pos_of_ne_zero hn),
      Nat.sub_add_cancel (Nat.pos_of_ne_zero hk)]⟩).elim

/-- Regroup a positive double series, with zero axes, into finite divisor sums. -/
theorem hasSum_mul_divisors {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℕ → ℕ → E} {a : E}
    (hf : HasSum (fun p : ℕ × ℕ => f (p.1 + 1) (p.2 + 1)) a)
    (hleft : ∀ n, f 0 n = 0) (hright : ∀ n, f n 0 = 0) :
    HasSum (fun m => ∑ d ∈ m.divisors, f d (m / d)) a := by
  have hfull := (hasSum_natProd_succ_iff hleft hright).mp hf
  have hgroup := hfull.tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)
  convert hgroup using 1
  funext m
  by_cases hm : m = 0
  · subst m
    simp only [Nat.divisors_zero, Finset.sum_empty]
    rw [← tsum_zero (β := (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0}) (α := E)]
    apply tsum_congr
    rintro ⟨⟨n, k⟩, hnk⟩
    change n * k = 0 at hnk
    rcases Nat.mul_eq_zero.mp hnk with hn | hk
    · simpa [hn] using (hleft k).symm
    · simpa [hk] using (hright n).symm
  · rw [show (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {m} = m.divisorsAntidiagonal by
      ext p
      simp [hm], Finset.tsum_subtype' m.divisorsAntidiagonal (fun p => f p.1 p.2)]
    exact (Nat.sum_divisorsAntidiagonal f).symm

end DirichletL

import Mathlib

/-!
Finite weight errors for CDT v2, supplied TeX 3503-3540 and 4150-4228.
Meanings and the signed calculation precede these bodies in
-/

namespace DirichletL

theorem sum_sum_abs_mul_sub_mul_le {κ : Type*} [Fintype κ] (α p : κ → ℝ)
    (hα : ∀ q, 0 ≤ α q) (hp : ∀ q, 0 ≤ p q)
    (hαsum : ∑ q, α q = 1) (hpsum : ∑ q, p q = 1) :
    (∑ q, ∑ r, |α q * α r - p q * p r|) ≤ 2 * ∑ q, |α q - p q| := by
  classical
  have hpoint (q r : κ) : |α q * α r - p q * p r| ≤
      α q * |α r - p r| + p r * |α q - p q| := by
    calc
      _ = |α q * (α r - p r) + p r * (α q - p q)| := by congr 1; ring
      _ ≤ |α q * (α r - p r)| + |p r * (α q - p q)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (hα q), abs_of_nonneg (hp r)]
  calc
    _ ≤ ∑ q, ∑ r, (α q * |α r - p r| + p r * |α q - p q|) :=
      Finset.sum_le_sum (fun q _ => Finset.sum_le_sum (fun r _ => hpoint q r))
    _ = 2 * ∑ q, |α q - p q| := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
        hαsum, hpsum, one_mul, mul_one, two_mul]

theorem abs_weighted_pair_sum_sub_le {κ : Type*} [Fintype κ] (α p : κ → ℝ)
    (hα : ∀ q, 0 ≤ α q) (hp : ∀ q, 0 ≤ p q)
    (hαsum : ∑ q, α q = 1) (hpsum : ∑ q, p q = 1)
    (A I : κ → κ → ℝ) {ξ B : ℝ} (hB : 0 ≤ B)
    (hAI : ∀ q r, |A q r - I q r| ≤ ξ) (hI : ∀ q r, |I q r| ≤ B) :
    |(∑ q, ∑ r, α q * α r * A q r) - (∑ q, ∑ r, p q * p r * I q r)| ≤
      ξ + 2 * B * ∑ q, |α q - p q| := by
  classical
  have habs (G : κ → κ → ℝ) : |∑ q, ∑ r, G q r| ≤ ∑ q, ∑ r, |G q r| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun q _ => Finset.abs_sum_le_sum_abs _ _))
  have hgrid : |(∑ q, ∑ r, α q * α r * A q r) -
      (∑ q, ∑ r, α q * α r * I q r)| ≤ ξ := by
    calc
      _ = |∑ q, ∑ r, α q * α r * (A q r - I q r)| := by
        simp only [mul_sub, Finset.sum_sub_distrib]
      _ ≤ ∑ q, ∑ r, |α q * α r * (A q r - I q r)| := habs _
      _ ≤ ∑ q, ∑ r, α q * α r * ξ := by
        apply Finset.sum_le_sum
        intro q _
        apply Finset.sum_le_sum
        intro r _
        rw [abs_mul, abs_of_nonneg (mul_nonneg (hα q) (hα r))]
        exact mul_le_mul_of_nonneg_left (hAI q r) (mul_nonneg (hα q) (hα r))
      _ = ξ := by
        simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hαsum,
          one_mul, mul_one]
  have hweight : |(∑ q, ∑ r, α q * α r * I q r) -
      (∑ q, ∑ r, p q * p r * I q r)| ≤ 2 * B * ∑ q, |α q - p q| := by
    calc
      _ = |∑ q, ∑ r, (α q * α r - p q * p r) * I q r| := by
        simp only [sub_mul, Finset.sum_sub_distrib]
      _ ≤ ∑ q, ∑ r, |(α q * α r - p q * p r) * I q r| := habs _
      _ ≤ ∑ q, ∑ r, |α q * α r - p q * p r| * B := by
        apply Finset.sum_le_sum
        intro q _
        apply Finset.sum_le_sum
        intro r _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hI q r) (abs_nonneg _)
      _ = (∑ q, ∑ r, |α q * α r - p q * p r|) * B := by
        simp only [Finset.sum_mul]
      _ ≤ (2 * ∑ q, |α q - p q|) * B :=
        mul_le_mul_of_nonneg_right (sum_sum_abs_mul_sub_mul_le α p hα hp hαsum hpsum) hB
      _ = 2 * B * ∑ q, |α q - p q| := by ring
  exact (abs_sub_le _ (∑ q, ∑ r, α q * α r * I q r) _).trans (add_le_add hgrid hweight)

end DirichletL

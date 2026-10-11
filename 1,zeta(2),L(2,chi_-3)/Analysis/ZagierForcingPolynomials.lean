import Analysis.ZagierODEPullback

/-!
Forcing polynomials derived from CDT v2, Lemma `defabc` and equation
`explicitode` (supplied TeX 7690-7750 and 8125-8140). The certificate combines
the source and conjugate left multiples. Formal descent is a separate step.
-/

noncomputable section

namespace DirichletL

open Polynomial

/-- The polynomial forcing of the literal B descent. -/
def zagierDescendedForcingB : ℚ[X] :=
  42 + 1506 * X + 3186 * X ^ 2 - 5520 * X ^ 3 + 1152 * X ^ 4

/-- The polynomial forcing of the literal C descent. -/
def zagierDescendedForcingC : ℚ[X] :=
  44 + 1288 * X + 18150 * X ^ 2 - 20752 * X ^ 3 + 4932 * X ^ 4 - 1296 * X ^ 5

theorem zagierForcedTrace_identity {K : Type*} [Field K] [Algebra ℚ K]
    (x u b c : K) (hu : (x - 1) * u = -1) :
    (x - 1) *
      (3 * (384 * x ^ 7 - 448 * x ^ 6 - 1066 * x ^ 5 + 1706 * x ^ 4 -
          1909 * x ^ 3 + 365 * x ^ 2 - 33 * x - 7) * (b + c * u) +
        (-1152 * x ^ 8 + 1728 * x ^ 7 + 2030 * x ^ 6 - 4760 * x ^ 5 +
          5757 * x ^ 4 - 2506 * x ^ 3 + 230 * x ^ 2 - 30 * x - 1) * (c * u ^ 2) +
        x * (x - 1) * (8 * x + 1) *
          (144 * x ^ 6 - 122 * x ^ 5 + 240 * x ^ 4 - 237 * x ^ 3 +
            121 * x ^ 2 - 3 * x + 1) * (2 * c * u ^ 3)) +
      (4 * (324 * x ^ 7 - 1224 * x ^ 6 + 1422 * x ^ 5 - 1049 * x ^ 4 +
          229 * x ^ 3 + 64 * x ^ 2 + 47 * x - 5) * (b * (x - 1) - c * (x - 1) ^ 2) -
        (1296 * x ^ 8 - 3168 * x ^ 7 + 24 * x ^ 6 + 3298 * x ^ 5 -
          4443 * x ^ 4 + 1812 * x ^ 3 - 8 * x ^ 2 + 38 * x - 1) * (b - 2 * c * (x - 1)) +
        (x - 1) * x * (9 * x - 1) *
          (144 * x ^ 6 - 122 * x ^ 5 + 240 * x ^ 4 - 237 * x ^ 3 +
            121 * x ^ 2 - 3 * x + 1) * (-2 * c)) =
      (x - 1) ^ 4 *
        (b * aeval (x + (1 - u)) zagierDescendedForcingB +
          c * aeval (x + (1 - u)) zagierDescendedForcingC) := by
  have hx : x - 1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hu
    exact one_ne_zero (neg_eq_zero.mp hu.symm)
  have hu' : u = -1 / (x - 1) := (eq_div_iff hx).mpr (by simpa [mul_comm] using hu)
  generalize ht : x - 1 = t at *
  have hxt : x = t + 1 := by linear_combination ht
  subst x
  rw [hu']
  simp only [zagierDescendedForcingB, zagierDescendedForcingC,
    map_add, map_sub, map_mul, map_pow, map_ofNat, aeval_X]
  field_simp [hx]
  ring

end DirichletL

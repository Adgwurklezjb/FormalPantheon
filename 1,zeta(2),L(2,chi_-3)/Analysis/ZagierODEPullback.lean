import Analysis.MobiusDerivatives

/-!
Polynomial pullback of CDT v2 equation `explicitode` along `y = x^2/(x-1)`.
The finite identities below certify left multiples of the Zagier operator
and its Mobius conjugate. They are checked by ring normalization.
-/

namespace DirichletL

/-- The five-jet polynomial for `(x-1)^3` times the pulled-back source operator. -/
def zagierPullbackJet {R : Type*} [CommRing R] (x f0 f1 f2 f3 f4 : R) : R :=
  -18 * (360 * x ^ 6 - 712 * x ^ 5 + 838 * x ^ 4 - 249 * x ^ 3 +
      117 * x ^ 2 + 9 * x - 3) * f0 +
    2 * (20736 * x ^ 9 - 33408 * x ^ 8 + 109596 * x ^ 7 - 197228 * x ^ 6 +
      191924 * x ^ 5 - 93357 * x ^ 4 + 17602 * x ^ 3 - 2480 * x ^ 2 +
      438 * x + 1) * f1 +
    2 * (72576 * x ^ 10 - 148032 * x ^ 9 + 299364 * x ^ 8 - 507205 * x ^ 7 +
      512598 * x ^ 6 - 280838 * x ^ 5 + 65408 * x ^ 4 - 4412 * x ^ 3 +
      899 * x ^ 2 + 11 * x - 1) * f2 +
    2 * x * (x - 1) * (41472 * x ^ 9 - 59904 * x ^ 8 + 107778 * x ^ 7 -
      144691 * x ^ 6 + 110269 * x ^ 5 - 34641 * x ^ 4 + 677 * x ^ 3 -
      214 * x ^ 2 - 12 * x + 2) * f3 +
    x ^ 2 * (x - 1) ^ 2 * (8 * x + 1) * (9 * x - 1) *
      (144 * x ^ 6 - 122 * x ^ 5 + 240 * x ^ 4 - 237 * x ^ 3 +
        121 * x ^ 2 - 3 * x + 1) * f4

theorem zagierPullbackJet_source {R : Type*} [CommRing R]
    (x f0 f1 f2 f3 f4 : R) :
    zagierPullbackJet x f0 f1 f2 f3 f4 =
      3 * (384 * x ^ 7 - 448 * x ^ 6 - 1066 * x ^ 5 + 1706 * x ^ 4 -
        1909 * x ^ 3 + 365 * x ^ 2 - 33 * x - 7) *
        (x * (1 - 10 * x + 9 * x ^ 2) * f2 +
          (1 - 20 * x + 27 * x ^ 2) * f1 + (9 * x - 3) * f0) +
      (-1152 * x ^ 8 + 1728 * x ^ 7 + 2030 * x ^ 6 - 4760 * x ^ 5 +
        5757 * x ^ 4 - 2506 * x ^ 3 + 230 * x ^ 2 - 30 * x - 1) *
        (x * (1 - 10 * x + 9 * x ^ 2) * f3 +
          2 * (1 - 20 * x + 27 * x ^ 2) * f2 + (63 * x - 23) * f1 + 9 * f0) +
      x * (x - 1) * (8 * x + 1) *
        (144 * x ^ 6 - 122 * x ^ 5 + 240 * x ^ 4 - 237 * x ^ 3 +
          121 * x ^ 2 - 3 * x + 1) *
        (x * (1 - 10 * x + 9 * x ^ 2) * f4 +
          3 * (1 - 20 * x + 27 * x ^ 2) * f3 + (171 * x - 63) * f2 + 72 * f1) := by
  dsimp [zagierPullbackJet]
  ring

theorem zagierPullbackJet_conjugate {R : Type*} [CommRing R]
    (x f0 f1 f2 f3 f4 : R) :
    (x - 1) * zagierPullbackJet x f0 f1 f2 f3 f4 =
      4 * (324 * x ^ 7 - 1224 * x ^ 6 + 1422 * x ^ 5 - 1049 * x ^ 4 +
        229 * x ^ 3 + 64 * x ^ 2 + 47 * x - 5) *
        (x * (x - 1) ^ 2 * (8 * x + 1) * f2 +
          (x - 1) * (8 * x ^ 2 - 16 * x - 1) * f1 + 3 * (2 * x + 1) * f0) -
      (1296 * x ^ 8 - 3168 * x ^ 7 + 24 * x ^ 6 + 3298 * x ^ 5 -
        4443 * x ^ 4 + 1812 * x ^ 3 - 8 * x ^ 2 + 38 * x - 1) *
        (x * (x - 1) ^ 2 * (8 * x + 1) * f3 +
          (40 * x ^ 3 - 69 * x ^ 2 + 27 * x + 2) * f2 +
          (24 * x ^ 2 - 42 * x + 18) * f1 + 6 * f0) +
      (x - 1) * x * (9 * x - 1) *
        (144 * x ^ 6 - 122 * x ^ 5 + 240 * x ^ 4 - 237 * x ^ 3 +
          121 * x ^ 2 - 3 * x + 1) *
        (x * (x - 1) ^ 2 * (8 * x + 1) * f4 +
          (72 * x ^ 3 - 114 * x ^ 2 + 39 * x + 3) * f3 +
          (144 * x ^ 2 - 180 * x + 45) * f2 + (48 * x - 36) * f1) := by
  dsimp [zagierPullbackJet]
  ring

local notation "D" => PowerSeries.derivative ℚ
local notation "x" => (PowerSeries.X : PowerSeries ℚ)

private theorem derivative_ofNat (n : ℕ) [n.AtLeastTwo] :
    D (ofNat(n) : PowerSeries ℚ) = 0 :=
  (PowerSeries.derivative ℚ).map_natCast n

/-- The polynomial fourth-order operator in the original coordinate. -/
noncomputable def zagierPullbackODE (f : PowerSeries ℚ) : PowerSeries ℚ :=
  zagierPullbackJet x f (D f) (D (D f)) (D (D (D f))) (D (D (D (D f))))

/-- The second-order Mobius conjugate of the Zagier equation. -/
noncomputable def zagierConjugateODE (f : PowerSeries ℚ) : PowerSeries ℚ :=
  x * (x - 1) ^ 2 * (8 * x + 1) * D (D f) +
    (x - 1) * (8 * x ^ 2 - 16 * x - 1) * D f + 3 * (2 * x + 1) * f

/-- The same left multiple retains the full forcing, including degree zero. -/
theorem zagierPullbackODE_eq_of_generatingODE {f r : PowerSeries ℚ}
    (hf : generatingODE f = r) :
    zagierPullbackODE f =
      3 * (384 * x ^ 7 - 448 * x ^ 6 - 1066 * x ^ 5 + 1706 * x ^ 4 -
        1909 * x ^ 3 + 365 * x ^ 2 - 33 * x - 7) * r +
      (-1152 * x ^ 8 + 1728 * x ^ 7 + 2030 * x ^ 6 - 4760 * x ^ 5 +
        5757 * x ^ 4 - 2506 * x ^ 3 + 230 * x ^ 2 - 30 * x - 1) * D r +
      x * (x - 1) * (8 * x + 1) *
        (144 * x ^ 6 - 122 * x ^ 5 + 240 * x ^ 4 - 237 * x ^ 3 +
          121 * x ^ 2 - 3 * x + 1) * D (D r) := by
  have h0 : x * (1 - 10 * x + 9 * x ^ 2) * D (D f) +
      (1 - 20 * x + 27 * x ^ 2) * D f + (9 * x - 3) * f = r := by
    simp only [generatingODE, map_ofNat, pow_one] at hf
    change x * (1 - 10 * x + 9 * x ^ 2) * f.derivativeFun.derivativeFun +
      (1 - 20 * x + 27 * x ^ 2) * f.derivativeFun + (9 * x - 3) * f = r
    linear_combination hf
  have h1 : x * (1 - 10 * x + 9 * x ^ 2) * D (D (D f)) +
      2 * (1 - 20 * x + 27 * x ^ 2) * D (D f) +
      (63 * x - 23) * D f + 9 * f = D r := by
    have h := congrArg D h0
    simp only [map_add, map_sub, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
      derivative_ofNat, Derivation.map_one_eq_zero, PowerSeries.derivative_X,
      smul_eq_mul, nsmul_eq_mul] at h
    norm_num at h
    linear_combination h
  have h2 : x * (1 - 10 * x + 9 * x ^ 2) * D (D (D (D f))) +
      3 * (1 - 20 * x + 27 * x ^ 2) * D (D (D f)) +
      (171 * x - 63) * D (D f) + 72 * D f = D (D r) := by
    have h := congrArg D h1
    simp only [map_add, map_sub, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
      derivative_ofNat, Derivation.map_one_eq_zero, PowerSeries.derivative_X,
      smul_eq_mul, nsmul_eq_mul] at h
    norm_num at h
    linear_combination h
  rw [zagierPullbackODE, zagierPullbackJet_source, h0, h1, h2]

theorem zagierPullbackODE_of_generatingODE {f : PowerSeries ℚ}
    (hf : generatingODE f = 0) : zagierPullbackODE f = 0 := by
  simpa only [map_zero, mul_zero, add_zero] using
    zagierPullbackODE_eq_of_generatingODE hf

/-- The conjugate left multiple with its actual, potentially nonzero forcing. -/
theorem X_sub_one_mul_zagierPullbackODE_eq {f r : PowerSeries ℚ}
    (hf : zagierConjugateODE f = r) :
    (x - 1) * zagierPullbackODE f =
      4 * (324 * x ^ 7 - 1224 * x ^ 6 + 1422 * x ^ 5 - 1049 * x ^ 4 +
        229 * x ^ 3 + 64 * x ^ 2 + 47 * x - 5) * r -
      (1296 * x ^ 8 - 3168 * x ^ 7 + 24 * x ^ 6 + 3298 * x ^ 5 -
        4443 * x ^ 4 + 1812 * x ^ 3 - 8 * x ^ 2 + 38 * x - 1) * D r +
      (x - 1) * x * (9 * x - 1) *
        (144 * x ^ 6 - 122 * x ^ 5 + 240 * x ^ 4 - 237 * x ^ 3 +
          121 * x ^ 2 - 3 * x + 1) * D (D r) := by
  have h0 := hf
  dsimp [zagierConjugateODE] at h0
  have h1 : x * (x - 1) ^ 2 * (8 * x + 1) * D (D (D f)) +
      (40 * x ^ 3 - 69 * x ^ 2 + 27 * x + 2) * D (D f) +
      (24 * x ^ 2 - 42 * x + 18) * D f + 6 * f = D r := by
    have h := congrArg D h0
    simp only [map_add, map_sub, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
      derivative_ofNat, Derivation.map_one_eq_zero, PowerSeries.derivative_X,
      smul_eq_mul, nsmul_eq_mul] at h
    norm_num at h
    linear_combination h
  have h2 : x * (x - 1) ^ 2 * (8 * x + 1) * D (D (D (D f))) +
      (72 * x ^ 3 - 114 * x ^ 2 + 39 * x + 3) * D (D (D f)) +
      (144 * x ^ 2 - 180 * x + 45) * D (D f) + (48 * x - 36) * D f = D (D r) := by
    have h := congrArg D h1
    simp only [map_add, map_sub, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
      derivative_ofNat, Derivation.map_one_eq_zero, PowerSeries.derivative_X,
      smul_eq_mul, nsmul_eq_mul] at h
    norm_num at h
    linear_combination h
  rw [zagierPullbackODE, zagierPullbackJet_conjugate, h0, h1, h2]

theorem zagierPullbackODE_of_conjugateODE {f : PowerSeries ℚ}
    (hf : zagierConjugateODE f = 0) : zagierPullbackODE f = 0 := by
  have hx : x - 1 ≠ 0 := by
    intro h
    have := congrArg (PowerSeries.constantCoeff (R := ℚ)) h
    norm_num at this
  apply (mul_eq_zero.mp (show (x - 1) * zagierPullbackODE f = 0 from ?_)).resolve_left hx
  simpa only [map_zero, mul_zero, sub_zero, add_zero] using
    X_sub_one_mul_zagierPullbackODE_eq hf

theorem zagierPullbackODE_add (f g : PowerSeries ℚ) :
    zagierPullbackODE (f + g) = zagierPullbackODE f + zagierPullbackODE g := by
  simp only [zagierPullbackODE, map_add, zagierPullbackJet]
  ring

end DirichletL

import Mathlib

/-!
The fixed residue polynomial in the regular-system specialization of CDT v2
`lem_Shidlovsky`, supplied TeX 2910-2935. Declaration meanings, native
-/

namespace DirichletL

theorem matrix_aeval_mul_eq_mul_aeval {ι σ R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [CommRing R]
    (H : Matrix ι ι R) (A : Matrix σ σ R) (B : Matrix ι σ R)
    (h : H * B = B * A) (p : Polynomial R) :
    Polynomial.aeval H p * B = B * Polynomial.aeval A p := by
  refine p.induction_on ?_ ?_ ?_
  · intro a
    simp only [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  · intro p q hp hq
    simp only [map_add, Matrix.add_mul, Matrix.mul_add, hp, hq]
  · intro n a ih
    have heq : Polynomial.C a * Polynomial.X ^ (n + 1) =
        (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by
      rw [pow_succ, mul_assoc]
    rw [heq, map_mul (Polynomial.aeval H) (Polynomial.C a * Polynomial.X ^ n) Polynomial.X,
      map_mul (Polynomial.aeval A) (Polynomial.C a * Polynomial.X ^ n) Polynomial.X]
    simp only [Polynomial.aeval_X]
    calc
      _ = Polynomial.aeval H (Polynomial.C a * Polynomial.X ^ n) * (H * B) :=
        Matrix.mul_assoc _ _ _
      _ = Polynomial.aeval H (Polynomial.C a * Polynomial.X ^ n) * (B * A) := by rw [h]
      _ = (Polynomial.aeval H (Polynomial.C a * Polynomial.X ^ n) * B) * A :=
        (Matrix.mul_assoc _ _ _).symm
      _ = (B * Polynomial.aeval A (Polynomial.C a * Polynomial.X ^ n)) * A := by rw [ih]
      _ = _ := Matrix.mul_assoc _ _ _

theorem matrix_aeval_eq_zero_of_intertwining {ι σ R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [CommRing R]
    (H : Matrix ι ι R) (A : Matrix σ σ R) (B : Matrix ι σ R)
    (J : ι → σ) (hBJ : B.submatrix id J = 1) (h : H * B = B * A)
    (p : Polynomial R) (hp : Polynomial.aeval A p = 0) :
    Polynomial.aeval H p = 0 := by
  have he := matrix_aeval_mul_eq_mul_aeval H A B h p
  rw [hp, Matrix.mul_zero] at he
  have hs := congrArg (fun M : Matrix ι σ R => M.submatrix id J) he
  simpa only [Matrix.submatrix_mul _ _ id id J Function.bijective_id,
    Matrix.submatrix_id_id, hBJ, Matrix.mul_one, Matrix.submatrix_zero] using hs

theorem matrix_aeval_charpoly_eq_zero_of_intertwining {ι σ R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [CommRing R]
    (H : Matrix ι ι R) (A : Matrix σ σ R) (B : Matrix ι σ R)
    (J : ι → σ) (hBJ : B.submatrix id J = 1) (h : H * B = B * A) :
    Polynomial.aeval H A.charpoly = 0 :=
  matrix_aeval_eq_zero_of_intertwining H A B J hBJ h A.charpoly A.aeval_self_charpoly

end DirichletL

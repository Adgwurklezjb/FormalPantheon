import Analysis.SortedIntegerMaximum

/-!
Structural kernel computation of CDT's signed contour numerator, author page 174.
The explicit fuel versions agree with Lean's canonical merge and merge sort.
-/

namespace DirichletL

/-- Merge whole integer bound/mass pairs with explicit structural fuel. -/
def mergeIntegerPairsWithFuel (fuel : ℕ) (xs ys : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  match fuel, xs, ys with
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | n + 1, x :: xs, y :: ys =>
    if x.1 ≤ y.1 then x :: mergeIntegerPairsWithFuel n xs (y :: ys)
    else y :: mergeIntegerPairsWithFuel n (x :: xs) ys

theorem mergeIntegerPairsWithFuel_eq_merge (fuel : ℕ) (xs ys : List (ℤ × ℤ))
    (h : xs.length + ys.length ≤ fuel) :
    mergeIntegerPairsWithFuel fuel xs ys =
      xs.merge ys (fun a b => decide (a.1 ≤ b.1)) := by
  induction fuel generalizing xs ys with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    subst ys
    simp [mergeIntegerPairsWithFuel]
  | succ fuel ih =>
    cases xs with
    | nil => simp [mergeIntegerPairsWithFuel]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeIntegerPairsWithFuel]
      | cons y ys =>
        have hx : xs.length + (y :: ys).length ≤ fuel := by
          simp only [List.length_cons] at h ⊢
          omega
        have hy : (x :: xs).length + ys.length ≤ fuel := by
          simp only [List.length_cons] at h ⊢
          omega
        by_cases hxy : x.1 ≤ y.1
        · simp [mergeIntegerPairsWithFuel, List.merge, hxy, ih xs (y :: ys) hx]
        · simp [mergeIntegerPairsWithFuel, List.merge, hxy, ih (x :: xs) ys hy]

/-- Balanced sorting of complete bound/mass pairs, with explicit recursion depth. -/
def sortIntegerPairsWithFuel (fuel : ℕ) (xs : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  match fuel, xs with
  | 0, xs => xs
  | _ + 1, [] => []
  | _ + 1, [x] => [x]
  | n + 1, x :: y :: xs =>
    let entries := x :: y :: xs
    let half := (entries.length + 1) / 2
    mergeIntegerPairsWithFuel entries.length
      (sortIntegerPairsWithFuel n (entries.take half))
      (sortIntegerPairsWithFuel n (entries.drop half))

theorem sortIntegerPairsWithFuel_eq_mergeSort (fuel : ℕ) (xs : List (ℤ × ℤ))
    (h : xs.length ≤ 2 ^ fuel) :
    sortIntegerPairsWithFuel fuel xs =
      xs.mergeSort (fun a b => decide (a.1 ≤ b.1)) := by
  induction fuel generalizing xs with
  | zero =>
    cases xs with
    | nil => simp [sortIntegerPairsWithFuel]
    | cons x xs =>
      have hx : xs = [] := List.length_eq_zero_iff.mp (by
        simp only [List.length_cons, pow_zero] at h
        omega)
      subst xs
      simp [sortIntegerPairsWithFuel]
  | succ fuel ih =>
    cases xs with
    | nil => simp [sortIntegerPairsWithFuel]
    | cons x xs =>
      cases xs with
      | nil => simp [sortIntegerPairsWithFuel]
      | cons y xs =>
        let entries := x :: y :: xs
        let half := (entries.length + 1) / 2
        have hleft : (entries.take half).length ≤ 2 ^ fuel := by
          rw [List.length_take]
          dsimp only [half, entries]
          rw [pow_succ] at h
          omega
        have hright : (entries.drop half).length ≤ 2 ^ fuel := by
          rw [List.length_drop]
          dsimp only [half, entries]
          rw [pow_succ] at h
          omega
        have hmerge :
            ((entries.take half).mergeSort (fun a b => decide (a.1 ≤ b.1))).length +
              ((entries.drop half).mergeSort (fun a b => decide (a.1 ≤ b.1))).length ≤
                entries.length := by
          simp only [List.length_mergeSort, List.length_take, List.length_drop]
          omega
        change mergeIntegerPairsWithFuel entries.length
          (sortIntegerPairsWithFuel fuel (entries.take half))
          (sortIntegerPairsWithFuel fuel (entries.drop half)) = _
        rw [ih _ hleft, ih _ hright, mergeIntegerPairsWithFuel_eq_merge _ _ _ hmerge]
        conv_rhs => rw [List.mergeSort]
        simp only [List.MergeSort.Internal.splitInTwo_fst,
          List.MergeSort.Internal.splitInTwo_snd, entries, half]

theorem sortedIntegerMaximum_eq_fold_sortIntegerPairsWithFuel
    (fuel : ℕ) (xs : List (ℤ × ℤ)) (h : xs.length ≤ 2 ^ fuel) :
    sortedIntegerMaximum xs = integerMaximumFold (sortIntegerPairsWithFuel fuel xs) 0 0 := by
  rw [sortIntegerPairsWithFuel_eq_mergeSort fuel xs h]
  rfl

end DirichletL

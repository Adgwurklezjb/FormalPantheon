import Analysis.WeightedPairwiseMaximum

/-!
Exact signed accumulation for CDT v2's double maximum, supplied TeX 3503-3538.
-/

namespace DirichletL

/-- Update cumulative mass and numerator with a signed bound and its mass. -/
def integerMaximumStep (state entry : ℤ × ℤ) : ℤ × ℤ :=
  (state.1 + entry.2,
    state.2 + entry.1 * (2 * state.1 * entry.2 + entry.2 * entry.2))

/-- Accumulate ordered bound/mass pairs from an arbitrary mass and numerator. -/
def integerMaximumFold (entries : List (ℤ × ℤ)) (W N : ℤ) : ℤ × ℤ :=
  entries.foldl integerMaximumStep (W, N)

/-- The integer double-maximum specification, retaining list multiplicities. -/
def integerPairwiseMaximum (entries : List (ℤ × ℤ)) : ℤ :=
  (entries.map fun entry =>
    (entries.map fun other => entry.2 * other.2 * max entry.1 other.1).sum).sum

theorem integerMaximumFold_fst (entries : List (ℤ × ℤ)) (W N : ℤ) :
    (integerMaximumFold entries W N).1 = W + (entries.map Prod.snd).sum := by
  induction entries generalizing W N with
  | nil => simp [integerMaximumFold]
  | cons entry entries ih =>
    change (integerMaximumFold entries (W + entry.2)
      (N + entry.1 * (2 * W * entry.2 + entry.2 * entry.2))).1 = _
    rw [ih]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem integerPairwiseMaximum_perm {entries other : List (ℤ × ℤ)}
    (h : entries.Perm other) :
    integerPairwiseMaximum entries = integerPairwiseMaximum other := by
  unfold integerPairwiseMaximum
  calc
    _ = (entries.map fun entry =>
        (other.map fun next => entry.2 * next.2 * max entry.1 next.1).sum).sum := by
      congr 1
      apply List.map_congr_left
      intro entry hentry
      exact (h.map (fun next => entry.2 * next.2 * max entry.1 next.1)).sum_eq
    _ = _ := (h.map (fun entry =>
      (other.map fun next => entry.2 * next.2 * max entry.1 next.1).sum)).sum_eq

theorem integerPairwiseMaximum_cons (entry : ℤ × ℤ)
    (entries : List (ℤ × ℤ))
    (h : ∀ other ∈ entries, entry.1 ≤ other.1) :
    integerPairwiseMaximum (entry :: entries) =
      entry.1 * entry.2 ^ 2 +
        2 * entry.2 * (entries.map (fun other => other.1 * other.2)).sum +
          integerPairwiseMaximum entries := by
  have hleft : (entries.map (fun other =>
      entry.2 * other.2 * max entry.1 other.1)).sum =
      entry.2 * (entries.map (fun other => other.1 * other.2)).sum := by
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro other hother
    rw [max_eq_right (h other hother)]
    ring
  have hright : (entries.map (fun other =>
      other.2 * entry.2 * max other.1 entry.1)).sum =
      entry.2 * (entries.map (fun other => other.1 * other.2)).sum := by
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro other hother
    rw [max_eq_left (h other hother)]
    ring
  simp only [integerPairwiseMaximum, List.map_cons, List.sum_cons, max_self,
    List.sum_map_add]
  rw [hleft, hright]
  ring

theorem integerMaximumFold_snd (entries : List (ℤ × ℤ))
    (h : entries.Pairwise (fun entry other => entry.1 ≤ other.1)) (W N : ℤ) :
    (integerMaximumFold entries W N).2 =
      N + 2 * W * (entries.map (fun entry => entry.1 * entry.2)).sum +
        integerPairwiseMaximum entries := by
  induction entries generalizing W N with
  | nil => simp [integerMaximumFold, integerPairwiseMaximum]
  | cons entry entries ih =>
    rcases List.pairwise_cons.mp h with ⟨hhead, htail⟩
    change (integerMaximumFold entries (W + entry.2)
      (N + entry.1 * (2 * W * entry.2 + entry.2 * entry.2))).2 = _
    rw [ih htail, integerPairwiseMaximum_cons entry entries hhead]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem integerMaximumFold_zero_snd (entries : List (ℤ × ℤ))
    (h : entries.Pairwise (fun entry other => entry.1 ≤ other.1)) :
    (integerMaximumFold entries 0 0).2 = integerPairwiseMaximum entries := by
  simpa only [mul_zero, zero_mul, zero_add] using integerMaximumFold_snd entries h 0 0

end DirichletL

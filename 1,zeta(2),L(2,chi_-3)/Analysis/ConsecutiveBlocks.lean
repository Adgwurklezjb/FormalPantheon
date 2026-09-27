import Analysis.ConsecutiveBlockBounds

/-!
Exact interval fibers for CDT v2, supplied TeX 3998-4028 and 4150-4179.
Meanings and empty-block checks precede these bodies in
-/

namespace DirichletL

/-- Coordinates in the half-open interval between two adjacent natural cuts. -/
def consecutiveBlock {s d : ℕ} (c : Fin (s + 1) → ℕ) (q : Fin s) : Finset (Fin d) :=
  Finset.univ.filter (fun i => c q.castSucc ≤ i.val ∧ i.val < c q.succ)

@[simp]
theorem mem_consecutiveBlock {s d : ℕ} (c : Fin (s + 1) → ℕ) (q : Fin s) (i : Fin d) :
    i ∈ consecutiveBlock c q ↔ c q.castSucc ≤ i.val ∧ i.val < c q.succ := by
  simp [consecutiveBlock]

theorem card_consecutiveBlock {s d : ℕ} (c : Fin (s + 1) → ℕ) (q : Fin s)
    (hcd : c q.succ ≤ d) :
    (consecutiveBlock (d := d) c q).card = consecutiveBlockSize c q := by
  rw [consecutiveBlockSize, ← Nat.card_Ico]
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    simpa only [Finset.mem_Ico, mem_consecutiveBlock] using hi
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro n hn
    have hnd : n < d := (Finset.mem_Ico.mp hn).2.trans_le hcd
    exact ⟨⟨n, hnd⟩, by simpa only [mem_consecutiveBlock, Finset.mem_Ico] using hn, rfl⟩

theorem exists_consecutiveBlock_map {s d : ℕ} (c : Fin (s + 1) → ℕ)
    (hc : Monotone c) (hc0 : c 0 = 0) (hcd : c (Fin.last s) = d) :
    ∃ b : Fin d → Fin s, ∀ i q, b i = q ↔ i ∈ consecutiveBlock c q := by
  classical
  let e (n : ℕ) := c ⟨min n s, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have he0 : e 0 = 0 := by simpa [e] using hc0
  have hes : e s = d := by simpa [e, Fin.last] using hcd
  have hex (i : Fin d) : ∃ q : Fin s, i ∈ consecutiveBlock c q := by
    have hi : i.val ∈ Set.Ico (e 0) (e s) := by
      rw [he0, hes]
      exact ⟨Nat.zero_le _, i.isLt⟩
    have hcover := Ico_subset_biUnion_Ico s e hi
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_Ico, exists_prop] at hcover
    obtain ⟨q, hq, hlo, hhi⟩ := hcover
    refine ⟨⟨q, hq⟩, ?_⟩
    simpa only [mem_consecutiveBlock, e, Nat.min_eq_left hq.le,
      Nat.min_eq_left (Nat.succ_le_of_lt hq)] using And.intro hlo hhi
  choose b hb using hex
  refine ⟨b, fun i q => ⟨fun h => h ▸ hb i, fun hq => ?_⟩⟩
  have hi := mem_consecutiveBlock c (b i) i |>.mp (hb i)
  have hj := mem_consecutiveBlock c q i |>.mp hq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hidx : (b i).succ ≤ q.castSucc := by
      change (b i).val + 1 ≤ q.val
      exact hlt
    have := hc hidx
    omega
  · have hidx : q.succ ≤ (b i).castSucc := by
      change q.val + 1 ≤ (b i).val
      exact hgt
    have := hc hidx
    omega

end DirichletL

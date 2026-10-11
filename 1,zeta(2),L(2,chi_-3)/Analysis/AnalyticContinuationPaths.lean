import Analysis.AnalyticContinuation

/-!
Parameter changes and restrictions to concatenated path segments preserve
actual analytic continuations. These connect the local forced periods to
the initial H germ in CDT v2, `functionsH` and `14functions`.
-/

namespace DirichletL

open Filter unitInterval
open scoped Topology

namespace AnalyticContinuationAlong

theorem reparam {T S : Type*} [TopologicalSpace T] [TopologicalSpace S]
    {γ : T → ℂ} {f : T → ℂ → ℂ} (hf : AnalyticContinuationAlong γ f)
    {φ : S → T} (hφ : Continuous φ) :
    AnalyticContinuationAlong (γ ∘ φ) (f ∘ φ) := by
  refine ⟨hf.continuous.comp hφ, fun s => hf.analytic (φ s), ?_⟩
  intro s
  exact hφ.continuousAt.tendsto.eventually (hf.locally_eq (φ s))

/-- Restrict a continuation to both concatenated paths, preserving exact joins and predicates. -/
theorem exists_trans_parts {X : Type*} [TopologicalSpace X] {x y z : X}
    (γ : Path x y) (δ : Path y z) (φ : X → ℂ) {F : I → ℂ → ℂ}
    (hF : AnalyticContinuationAlong (fun t => φ ((γ.trans δ) t)) F)
    (P : X → (ℂ → ℂ) → Prop) (hP : ∀ t, P ((γ.trans δ) t) (F t)) :
    ∃ G H : I → ℂ → ℂ,
      AnalyticContinuationAlong (fun t => φ (γ t)) G ∧
      AnalyticContinuationAlong (fun t => φ (δ t)) H ∧
      G 0 = F 0 ∧ H 1 = F 1 ∧ G 1 = H 0 ∧
      (∀ t, P (γ t) (G t)) ∧ ∀ t, P (δ t) (H t) := by
  let L : C(I, I) := {
    toFun t := ⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩
    continuous_toFun := (by fun_prop : Continuous (fun t : I => (t : ℝ) / 2)).subtype_mk
      (fun t => by constructor <;> linarith [t.2.1, t.2.2]) }
  let R : C(I, I) := {
    toFun t := ⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩
    continuous_toFun := (by fun_prop : Continuous (fun t : I => ((t : ℝ) + 1) / 2)).subtype_mk
      (fun t => by constructor <;> linarith [t.2.1, t.2.2]) }
  have hL (t : I) : (γ.trans δ) (L t) = γ t := by
    rw [Path.trans_apply, dif_pos (show (L t : ℝ) ≤ 1 / 2 by dsimp [L]; linarith [t.2.2])]
    congr 1
    apply Subtype.ext
    dsimp [L]
    ring
  have hR (t : I) : (γ.trans δ) (R t) = δ t := by
    by_cases ht : t = 0
    · subst t
      rw [Path.trans_apply, dif_pos (by norm_num [R])]
      have he : (⟨2 * (R 0 : ℝ), by norm_num [R, Set.mem_Icc]⟩ : I) = 1 := by
        apply Subtype.ext
        norm_num [R]
      rw [he, Path.target, Path.source]
    · have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (by
        intro he
        exact ht (Subtype.ext he.symm))
      rw [Path.trans_apply, dif_neg (show ¬(R t : ℝ) ≤ 1 / 2 by dsimp [R]; linarith)]
      congr 1
      apply Subtype.ext
      dsimp [R]
      ring
  have hL0 : L 0 = 0 := by apply Subtype.ext; norm_num [L]
  have hR1 : R 1 = 1 := by apply Subtype.ext; norm_num [R]
  have hLR : L 1 = R 0 := by apply Subtype.ext; norm_num [L, R]
  refine ⟨F ∘ L, F ∘ R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Function.comp_def, hL] using hF.reparam L.continuous
  · simpa only [Function.comp_def, hR] using hF.reparam R.continuous
  · simp only [Function.comp_apply, hL0]
  · simp only [Function.comp_apply, hR1]
  · simp only [Function.comp_apply, hLR]
  · intro t
    simpa only [hL, Function.comp_apply] using hP (L t)
  · intro t
    simpa only [hR, Function.comp_apply] using hP (R t)

end AnalyticContinuationAlong

end DirichletL

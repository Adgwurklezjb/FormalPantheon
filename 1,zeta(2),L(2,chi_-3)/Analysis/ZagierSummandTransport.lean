import Analysis.ZagierSolutionSummands
import Analysis.ZagierSummandContinuation

/-!
Actual path transport preserves the source and conjugate summands over the x-plane.
The restriction to a fixed sheet is essential in CDT v2's `14functions` argument.
-/

namespace DirichletL

open unitInterval

theorem zagierPathTransport_mem_sourceSummand (b : zagierODERegularSet)
    {x y : ℂ} (δ : Path x y) (h₁ : ∀ t, δ t ≠ 1)
    (hreg : ∀ t, mobiusCoordinate (δ t) ∈ zagierODERegularSet)
    (hx₁ : x ≠ 1) (hy₁ : y ≠ 1)
    {φ : zagierSolutionGerms (mobiusCoordinate x)} (hφ : φ ∈ zagierSourceSummand hx₁) :
    zagierPathTransport b (zagierMobiusPath δ h₁ hreg) φ ∈ zagierSourceSummand hy₁ := by
  obtain ⟨f, _, hE, hf⟩ := hφ
  exact exists_zagierPathTransport_secondOrder_rep b δ h₁ hreg hx₁ hy₁ φ hE hf

theorem zagierPathTransport_mem_conjugateSummand (b : zagierODERegularSet)
    {x y : ℂ} (δ : Path x y) (h₁ : ∀ t, δ t ≠ 1)
    (hreg : ∀ t, mobiusCoordinate (δ t) ∈ zagierODERegularSet)
    (hx₁ : x ≠ 1) (hy₁ : y ≠ 1)
    {φ : zagierSolutionGerms (mobiusCoordinate x)} (hφ : φ ∈ zagierConjugateSummand hx₁) :
    zagierPathTransport b (zagierMobiusPath δ h₁ hreg) φ ∈ zagierConjugateSummand hy₁ := by
  obtain ⟨f, _, hC, hf⟩ := hφ
  exact exists_zagierPathTransport_conjugate_rep b δ h₁ hreg hx₁ hy₁ φ hC hf

theorem zagierPathTransport_mem_sourceSummand_iff (b : zagierODERegularSet)
    {x y : ℂ} (δ : Path x y) (h₁ : ∀ t, δ t ≠ 1)
    (hreg : ∀ t, mobiusCoordinate (δ t) ∈ zagierODERegularSet)
    (hx₁ : x ≠ 1) (hy₁ : y ≠ 1) (φ : zagierSolutionGerms (mobiusCoordinate x)) :
    zagierPathTransport b (zagierMobiusPath δ h₁ hreg) φ ∈ zagierSourceSummand hy₁ ↔
      φ ∈ zagierSourceSummand hx₁ := by
  constructor
  · intro hφ
    have hback := zagierPathTransport_mem_sourceSummand b δ.symm
      (fun t => h₁ (σ t)) (fun t => hreg (σ t)) hy₁ hx₁ hφ
    simpa only [zagierMobiusPath_symm, zagierPathTransport_symm] using hback
  · exact zagierPathTransport_mem_sourceSummand b δ h₁ hreg hx₁ hy₁

theorem zagierPathTransport_mem_conjugateSummand_iff (b : zagierODERegularSet)
    {x y : ℂ} (δ : Path x y) (h₁ : ∀ t, δ t ≠ 1)
    (hreg : ∀ t, mobiusCoordinate (δ t) ∈ zagierODERegularSet)
    (hx₁ : x ≠ 1) (hy₁ : y ≠ 1) (φ : zagierSolutionGerms (mobiusCoordinate x)) :
    zagierPathTransport b (zagierMobiusPath δ h₁ hreg) φ ∈ zagierConjugateSummand hy₁ ↔
      φ ∈ zagierConjugateSummand hx₁ := by
  constructor
  · intro hφ
    have hback := zagierPathTransport_mem_conjugateSummand b δ.symm
      (fun t => h₁ (σ t)) (fun t => hreg (σ t)) hy₁ hx₁ hφ
    simpa only [zagierMobiusPath_symm, zagierPathTransport_symm] using hback
  · exact zagierPathTransport_mem_conjugateSummand b δ h₁ hreg hx₁ hy₁

end DirichletL

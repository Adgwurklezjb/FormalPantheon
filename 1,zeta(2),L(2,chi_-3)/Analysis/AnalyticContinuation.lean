import Mathlib

/-!
Compatible local analytic representatives along a continuous base curve.
This supplies explicit continuations for the monodromy step in CDT v2,
Lemma `14functions`, without requiring a global scalar representative.
-/

namespace DirichletL

open Filter Set
open scoped Topology

/-- A continuous curve with analytic representatives that agree locally as full germs. -/
structure AnalyticContinuationAlong {T : Type*} [TopologicalSpace T]
    (γ : T → ℂ) (f : T → ℂ → ℂ) : Prop where
  continuous : Continuous γ
  analytic : ∀ t, AnalyticAt ℂ (f t) (γ t)
  locally_eq : ∀ t, ∀ᶠ s in 𝓝 t, f s =ᶠ[𝓝 (γ s)] f t

namespace AnalyticContinuationAlong

variable {T : Type*} [TopologicalSpace T] {γ : T → ℂ} {f g : T → ℂ → ℂ}

theorem const (hγ : Continuous γ) {F : ℂ → ℂ} (hF : ∀ t, AnalyticAt ℂ F (γ t)) :
    AnalyticContinuationAlong γ (fun _ => F) :=
  ⟨hγ, hF, fun _ => Filter.Eventually.of_forall (fun _ => Filter.EventuallyEq.rfl)⟩

theorem deriv (hf : AnalyticContinuationAlong γ f) :
    AnalyticContinuationAlong γ (fun t => _root_.deriv (f t)) := by
  refine ⟨hf.continuous, fun t => (hf.analytic t).deriv, ?_⟩
  intro t
  filter_upwards [hf.locally_eq t] with s hs
  exact hs.deriv

theorem add (hf : AnalyticContinuationAlong γ f) (hg : AnalyticContinuationAlong γ g) :
    AnalyticContinuationAlong γ (fun t z => f t z + g t z) := by
  refine ⟨hf.continuous, fun t => (hf.analytic t).add (hg.analytic t), ?_⟩
  intro t
  filter_upwards [hf.locally_eq t, hg.locally_eq t] with s hfs hgs
  exact hfs.add hgs

theorem mul (hf : AnalyticContinuationAlong γ f) (hg : AnalyticContinuationAlong γ g) :
    AnalyticContinuationAlong γ (fun t z => f t z * g t z) := by
  refine ⟨hf.continuous, fun t => (hf.analytic t).mul (hg.analytic t), ?_⟩
  intro t
  filter_upwards [hf.locally_eq t, hg.locally_eq t] with s hfs hgs
  exact hfs.mul hgs

theorem congr (hf : AnalyticContinuationAlong γ f)
    (he : ∀ t, f t =ᶠ[𝓝 (γ t)] g t) : AnalyticContinuationAlong γ g := by
  refine ⟨hf.continuous, fun t => (hf.analytic t).congr (he t), ?_⟩
  intro t
  have hn := hf.continuous.continuousAt.tendsto.eventually (he t).eventually_nhds
  filter_upwards [hf.locally_eq t, hn] with s hs hns
  exact (he s).symm.trans (hs.trans hns)

theorem comp (hf : AnalyticContinuationAlong γ f) {δ : T → ℂ} {φ : ℂ → ℂ}
    (hδ : Continuous δ) (hφ : ∀ t, AnalyticAt ℂ φ (δ t))
    (he : ∀ t, φ (δ t) = γ t) :
    AnalyticContinuationAlong δ (fun t z => f t (φ z)) := by
  refine ⟨hδ, ?_, ?_⟩
  · intro t
    exact (hf.analytic t).comp_of_eq (hφ t) (he t)
  · intro t
    filter_upwards [hf.locally_eq t] with s hs
    exact hs.comp_tendsto (by simpa only [he s] using (hφ s).continuousAt.tendsto)

theorem isLocallyConstant_eq (hf : AnalyticContinuationAlong γ f)
    (hg : AnalyticContinuationAlong γ g) :
    IsLocallyConstant (fun t => f t =ᶠ[𝓝 (γ t)] g t) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro t
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((hf.analytic t).eventually_analyticAt.and (hg.analytic t).eventually_analyticAt)
  have hF : AnalyticOnNhd ℂ (f t) (Metric.ball (γ t) r) := fun z hz => (hball hz).1
  have hG : AnalyticOnNhd ℂ (g t) (Metric.ball (γ t) r) := fun z hz => (hball hz).2
  have hn := hf.continuous.continuousAt.tendsto.eventually (Metric.ball_mem_nhds (γ t) hr)
  filter_upwards [hf.locally_eq t, hg.locally_eq t, hn] with s hfs hgs hs
  apply propext
  constructor
  · intro he
    have he' := hF.eqOn_of_preconnected_of_eventuallyEq hG
      (convex_ball (γ t) r).isPreconnected hs (hfs.symm.trans (he.trans hgs))
    exact Filter.eventually_of_mem (Metric.ball_mem_nhds (γ t) hr) (fun z hz => he' hz)
  · intro he
    have he' := hF.eqOn_of_preconnected_of_eventuallyEq hG
      (convex_ball (γ t) r).isPreconnected (Metric.mem_ball_self hr) he
    have hev : f t =ᶠ[𝓝 (γ s)] g t :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hs) (fun z hz => he' hz)
    exact hfs.trans (hev.trans hgs.symm)

theorem eq_of_preconnectedSpace [PreconnectedSpace T]
    (hf : AnalyticContinuationAlong γ f) (hg : AnalyticContinuationAlong γ g)
    {t₀ : T} (he : f t₀ =ᶠ[𝓝 (γ t₀)] g t₀) (t : T) : f t =ᶠ[𝓝 (γ t)] g t := by
  have h := (hf.isLocallyConstant_eq hg).apply_eq_of_preconnectedSpace t t₀
  exact h.mpr he

end AnalyticContinuationAlong

end DirichletL

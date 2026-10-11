import Analysis.ZagierOriginalPaths
import Analysis.ZagierEndpointMonodromy
import Analysis.ZagierConjugateLoops

/-!
Actual original paths realizing the two shears, with a controlled endpoint
radius and unit-disk containment, for CDT v2, `14functions` (TeX 8074-8100).
-/

namespace DirichletL

open Filter Set unitInterval
open scoped Topology

theorem exists_zagierOriginal_origin_shear {q : ℝ} (hq : q ∈ Ioo 0 (1 / 9 : ℝ))
    (b : zagierODERegularSet) :
    ∃ γ : Path (⟨q, zagierEndpointInterval_mem_pullback hq⟩ : zagierPullbackRegularSet)
        ⟨q, zagierEndpointInterval_mem_pullback hq⟩,
      (∀ t, ‖(γ t : ℂ)‖ < 1) ∧ ∃ k : ℂ, k ≠ 0 ∧
        ∀ φ ψ : zagierSolutionGerms (mobiusCoordinate q),
          mobiusGermPullback (zagierEndpointInterval_noncritical hq).2.1
            (φ : Germ (𝓝 (mobiusCoordinate q)) ℂ) = zagierAnalytic →
          mobiusGermPullback (zagierEndpointInterval_noncritical hq).2.1
            (ψ : Germ (𝓝 (mobiusCoordinate q)) ℂ) = zagierEndpointSolution →
          zagierPathTransport b (γ.map zagierPullbackProjection.continuous) φ = φ ∧
          zagierPathTransport b (γ.map zagierPullbackProjection.continuous) ψ = ψ + k • φ := by
  obtain ⟨s, hs, γ, hγ, k, hk, hshear⟩ := exists_zagierEndpoint_circle_transport_shear b
  have hreg (t : I) : complexCirclePath s t ∈ zagierPullbackRegularSet := by
    refine ⟨complexCirclePath_ne_one (by rw [abs_of_pos hs.1]; linarith [hs.2]) t, ?_⟩
    rw [← hγ t]
    exact (γ t).property
  let δ := zagierPullbackPath (complexCirclePath s) hreg
  let η := zagierPullbackIntervalPath hq hs
  have hδ : δ.map zagierPullbackProjection.continuous = γ := by
    apply Path.ext
    funext t
    exact Subtype.ext (hγ t).symm
  have hη : η.map zagierPullbackProjection.continuous = zagierEndpointPath hq hs :=
    zagierPullbackIntervalPath_projection hq hs
  have hηnorm : range η ⊆ {z : zagierPullbackRegularSet | ‖(z : ℂ)‖ < 1} :=
    range_subset_iff.mpr (norm_zagierPullbackIntervalPath_lt_one hq hs)
  have hδnorm : range δ ⊆ {z : zagierPullbackRegularSet | ‖(z : ℂ)‖ < 1} := by
    apply range_subset_iff.mpr
    intro t
    change ‖complexCirclePath s t‖ < 1
    rw [norm_complexCirclePath, abs_of_pos hs.1]
    linarith [hs.2]
  refine ⟨(η.trans δ).trans η.symm, ?_, k, hk, ?_⟩
  · have hn : range ((η.trans δ).trans η.symm) ⊆
        {z : zagierPullbackRegularSet | ‖(z : ℂ)‖ < 1} := by
      rw [Path.trans_range, Path.trans_range, Path.symm_range]
      exact union_subset (union_subset hηnorm hδnorm) hηnorm
    exact fun t => hn (mem_range_self t)
  · intro φ ψ hφ hψ
    obtain ⟨hφs, hψs⟩ := hshear
      (zagierPathTransport b (zagierEndpointPath hq hs) φ)
      (zagierPathTransport b (zagierEndpointPath hq hs) ψ)
      (mobiusGermPullback_zagierEndpointPath b hq hs
        (fun _ hu => (zagierEndpointInterval_solutions hu).1)
        (fun _ hu => (zagierEndpointInterval_solutions hu).2.1) φ hφ)
      (mobiusGermPullback_zagierEndpointPath b hq hs
        (fun _ hu => (zagierEndpointInterval_solutions hu).2.2.1)
        (fun _ hu => (zagierEndpointInterval_solutions hu).2.2.2) ψ hψ)
    simp only [Path.map_trans, ← Path.map_symm, hδ, hη]
    constructor
    · rw [zagierPathTransport_trans, zagierPathTransport_trans, hφs, zagierPathTransport_symm]
    · rw [zagierPathTransport_trans, zagierPathTransport_trans, hψs,
        zagierPathTransport_add, zagierPathTransport_smul,
        zagierPathTransport_symm, zagierPathTransport_symm]

theorem exists_zagierOriginal_endpoint_shear_lt (b : zagierODERegularSet)
    {R : ℝ} (hR : 0 < R) :
    ∃ q : ℝ, ∃ hq : q ∈ Ioo 0 (1 / 9 : ℝ), ∃ r : ℝ, ∃ hr : r ∈ Ioo 0 (1 / 9 : ℝ),
      r < R ∧ q = (1 - 9 * r) / (9 * (1 - r)) ∧
      ∃ γ : Path (⟨q, zagierEndpointInterval_mem_pullback hq⟩ : zagierPullbackRegularSet)
          ⟨q, zagierEndpointInterval_mem_pullback hq⟩,
        (∀ t, (γ t : ℂ) = zagierEndpointCirclePath r hr t) ∧
        (∀ t, ‖(γ t : ℂ)‖ < 1) ∧ ∃ k : ℂ, k ≠ 0 ∧
          ∀ φ ψ : zagierSolutionGerms (mobiusCoordinate q),
            mobiusGermPullback (zagierEndpointInterval_noncritical hq).2.1
              (φ : Germ (𝓝 (mobiusCoordinate q)) ℂ) = zagierAnalytic →
            mobiusGermPullback (zagierEndpointInterval_noncritical hq).2.1
              (ψ : Germ (𝓝 (mobiusCoordinate q)) ℂ) = zagierEndpointSolution →
            zagierPathTransport b (γ.map zagierPullbackProjection.continuous) φ = φ + k • ψ ∧
            zagierPathTransport b (γ.map zagierPullbackProjection.continuous) ψ = ψ := by
  obtain ⟨S, hS, hsmall⟩ := exists_zagierEndpointCircle_radius_subset_ball
    (R := 1 / 2) (by norm_num)
  obtain ⟨q, hq, r, hr, hrRS, hqr, γ, hγ, k, hk, hshear⟩ :=
    exists_zagierEndpoint_endpointCircle_transport_shear_lt b (lt_min hR hS)
  have he : (q : ℂ) = zagierEndpointCoordinate (r : ℂ) :=
    (congrArg (fun s : ℝ => (s : ℂ)) hqr).trans (zagierEndpointCoordinate_ofReal r).symm
  let δ : Path (q : ℂ) (q : ℂ) := (zagierEndpointCirclePath r hr).cast he he
  have hreg (t : I) : δ t ∈ zagierPullbackRegularSet := by
    refine ⟨zagierEndpointCoordinate_ne_one
      (complexCirclePath_ne_one (by rw [abs_of_pos hr.1]; linarith [hr.2]) t), ?_⟩
    rw [show mobiusCoordinate (δ t) = (γ t : ℂ) from (hγ t).symm]
    exact (γ t).property
  let τ := zagierPullbackPath δ hreg
  have hτ : τ.map zagierPullbackProjection.continuous = γ := by
    apply Path.ext
    funext t
    exact Subtype.ext (hγ t).symm
  refine ⟨q, hq, r, hr, hrRS.trans_le (min_le_left _ _), hqr, τ, fun _ => rfl, ?_,
    k, hk, ?_⟩
  · intro t
    have hd := hsmall r hr (hrRS.trans_le (min_le_right _ _)) t
    change ‖δ t‖ < 1
    have hn : ‖δ t - (1 / 9 : ℂ)‖ < 1 / 2 := hd
    have ht := norm_add_le (δ t - (1 / 9 : ℂ)) (1 / 9 : ℂ)
    rw [sub_add_cancel] at ht
    norm_num at ht
    linarith
  · simpa only [hτ] using hshear

theorem not_fixed_of_two_linear_shears {V : Type*} [AddCommGroup V] [Module ℂ V]
    (U V' : V →ₗ[ℂ] V) {u v : V} {k l : ℂ}
    (hUu : U u = u) (hUv : U v = v + k • u)
    (hVu : V' u = u + l • v) (hVv : V' v = v) (hk : k ≠ 0) (hl : l ≠ 0)
    (hind : LinearIndependent ℂ ![u, v]) {d : V}
    (hd : d ∈ Submodule.span ℂ {u, v}) (hne : d ≠ 0) :
    V' d ≠ d ∨ V' (U d) ≠ U d := by
  have hi (a b : ℂ) (he : a • u + b • v = 0) : a = 0 ∧ b = 0 := by
    have hz := Fintype.linearIndependent_iff.mp hind ![a, b] (by
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] using he)
    exact ⟨hz 0, hz 1⟩
  have hi' (a b : ℂ) (he : a • v + b • u = 0) : a = 0 ∧ b = 0 :=
    (hi b a (by simpa only [add_comm] using he)).symm
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hd
  by_contra h
  push_neg at h
  have ha : a = 0 := eq_zero_coefficient_of_linear_shear V' hVv hVu hl hi'
    (a := b) (b := a) (c := 1) (by simpa only [add_comm, one_smul] using h.1)
  have hUd : U (a • u + b • v) = (a + b * k) • u + b • v := by
    rw [map_add, map_smul, map_smul, hUu, hUv]
    simp only [add_smul, mul_smul, smul_add]
    abel
  have hab : a + b * k = 0 := eq_zero_coefficient_of_linear_shear V' hVv hVu hl hi'
    (a := b) (b := a + b * k) (c := 1)
    (by simpa only [hUd, add_comm, one_smul] using h.2)
  have hb : b = 0 := (mul_eq_zero.mp (by simpa only [ha, zero_add] using hab)).resolve_right hk
  exact hne (by simp only [ha, hb, zero_smul, add_zero])

end DirichletL

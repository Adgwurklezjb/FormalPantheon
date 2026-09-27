import Analysis.ZagierEndpointInterval
import Analysis.ZagierMonodromy
import Analysis.AnalyticContinuationLinear

/-!
The two endpoint shears on actual fourth-order solution germs, compared
at a common regular base for the monodromy step of CDT v2, `14functions`.
-/

namespace DirichletL

open Filter Set unitInterval
open scoped Topology

attribute [local instance] Path.Homotopic.setoid

theorem exists_zagierEndpoint_circle_transport_shear (b : zagierODERegularSet) :
    ∃ r : ℝ, ∃ hr : r ∈ Ioo 0 (1 / 9 : ℝ),
      ∃ γ : Path (⟨mobiusCoordinate r, mobiusCoordinate_regular_of_mem_Ioo hr⟩ : zagierODERegularSet)
        ⟨mobiusCoordinate r, mobiusCoordinate_regular_of_mem_Ioo hr⟩,
      (∀ t, (γ t : ℂ) = mobiusCoordinate (complexCirclePath r t)) ∧
      ∃ k : ℂ, k ≠ 0 ∧ ∀ φ ψ : zagierSolutionGerms (mobiusCoordinate r),
        mobiusGermPullback (zagierEndpointInterval_noncritical hr).2.1
          (φ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = zagierAnalytic →
        mobiusGermPullback (zagierEndpointInterval_noncritical hr).2.1
          (ψ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = zagierEndpointSolution →
        zagierPathTransport b γ φ = φ ∧ zagierPathTransport b γ ψ = ψ + k • φ := by
  obtain ⟨R, hR, hregular⟩ := exists_zagierPullback_circle_radius
  obtain ⟨r, hr, hrR, c, hc, f, hf, hE, hf₀, hf₁, _⟩ :=
    exists_zagierEndpointSolution_continuation_lt hR
  obtain ⟨hr₀, hr₁, hr₂⟩ := zagierEndpointInterval_noncritical hr
  have h₁ (t : I) : complexCirclePath r t ≠ 1 :=
    complexCirclePath_ne_one (by rw [abs_of_pos hr.1]; linarith [hr.2]) t
  have hreg (t : I) : mobiusCoordinate (complexCirclePath r t) ∈ zagierODERegularSet :=
    (hregular r hr hrR t).1
  have h₀ (t : I) : complexCirclePath r t ≠ 0 :=
    (mobiusCoordinate_regular_ne_zero_two (hreg t)).1
  have h₂ (t : I) : complexCirclePath r t ≠ 2 :=
    (mobiusCoordinate_regular_ne_zero_two (hreg t)).2
  have hnorm (t : I) : ‖complexCirclePath r t‖ < 1 / 9 := by
    rw [norm_complexCirclePath, abs_of_pos hr.1]
    exact hr.2
  have hH := AnalyticContinuationAlong.const (complexCirclePath r).continuous
    (fun t => analyticAt_zagierAnalytic (hnorm t))
  have hHE (t : I) : zagierSecondOrderODE zagierAnalytic =ᶠ[𝓝 (complexCirclePath r t)] 0 := by
    filter_upwards [continuous_norm.continuousAt.eventually_lt_const (hnorm t)] with z hz
    exact zagierAnalytic_ode hz
  let γ := zagierMobiusPath (complexCirclePath r) h₁ hreg
  let k : ℂ := c * (2 * Real.pi * Complex.I)
  have hk : k ≠ 0 := mul_ne_zero hc (mul_ne_zero
    (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  refine ⟨r, hr, γ, fun _ => rfl, k, hk, ?_⟩
  intro φ ψ hφ hψ
  constructor
  · apply Subtype.ext
    apply mobiusGermPullback_injective hr₀ hr₁ hr₂
    exact (mobiusGermPullback_zagierPathTransport b (complexCirclePath r) h₁ hreg hr₁ hr₁
      hH hHE h₀ h₂ φ hφ).trans hφ.symm
  · apply Subtype.ext
    apply mobiusGermPullback_injective hr₀ hr₁ hr₂
    have ht := mobiusGermPullback_zagierPathTransport b (complexCirclePath r) h₁ hreg hr₁ hr₁
      hf hE h₀ h₂ ψ (hψ.trans (Germ.coe_eq.mpr hf₀.symm))
    rw [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, hψ, hφ]
    exact ht.trans (Germ.coe_eq.mpr hf₁)

theorem exists_zagierEndpoint_endpointCircle_transport_shear_lt (b : zagierODERegularSet)
    {R : ℝ} (hR : 0 < R) :
    ∃ q : ℝ, ∃ hq : q ∈ Ioo 0 (1 / 9 : ℝ), ∃ r : ℝ, ∃ hr : r ∈ Ioo 0 (1 / 9 : ℝ),
      r < R ∧ q = (1 - 9 * r) / (9 * (1 - r)) ∧
      ∃ γ : Path (⟨mobiusCoordinate q, mobiusCoordinate_regular_of_mem_Ioo hq⟩ : zagierODERegularSet)
        ⟨mobiusCoordinate q, mobiusCoordinate_regular_of_mem_Ioo hq⟩,
      (∀ t, (γ t : ℂ) = mobiusCoordinate (zagierEndpointCirclePath r hr t)) ∧
      ∃ k : ℂ, k ≠ 0 ∧ ∀ φ ψ : zagierSolutionGerms (mobiusCoordinate q),
        mobiusGermPullback (zagierEndpointInterval_noncritical hq).2.1
          (φ : Germ (𝓝 (mobiusCoordinate q)) ℂ) = zagierAnalytic →
        mobiusGermPullback (zagierEndpointInterval_noncritical hq).2.1
          (ψ : Germ (𝓝 (mobiusCoordinate q)) ℂ) = zagierEndpointSolution →
        zagierPathTransport b γ φ = φ + k • ψ ∧ zagierPathTransport b γ ψ = ψ := by
  obtain ⟨S, hS, hregular⟩ := exists_zagierPullback_circle_radius
  obtain ⟨r, hr, hrR, c, hc, f, hf, hE, hf₀, hf₁, _⟩ :=
    exists_zagierAnalytic_endpointContinuation_lt (lt_min hR hS)
  let q : ℝ := (1 - 9 * r) / (9 * (1 - r))
  have hq : q ∈ Ioo 0 (1 / 9 : ℝ) := zagierEndpointCoordinate_mem_Ioo hr
  have he : (q : ℂ) = zagierEndpointCoordinate (r : ℂ) :=
    (zagierEndpointCoordinate_ofReal r).symm
  let δ : Path (q : ℂ) (q : ℂ) := (zagierEndpointCirclePath r hr).cast he he
  have h₁ (t : I) : δ t ≠ 1 := by
    change zagierEndpointCoordinate (complexCirclePath r t) ≠ 1
    exact zagierEndpointCoordinate_ne_one
      (complexCirclePath_ne_one (by rw [abs_of_pos hr.1]; linarith [hr.2]) t)
  have hreg (t : I) : mobiusCoordinate (δ t) ∈ zagierODERegularSet :=
    (hregular r hr (hrR.trans_le (min_le_right R S)) t).2
  have h₀ (t : I) : δ t ≠ 0 := (mobiusCoordinate_regular_ne_zero_two (hreg t)).1
  have h₂ (t : I) : δ t ≠ 2 := (mobiusCoordinate_regular_ne_zero_two (hreg t)).2
  have hnorm (t : I) : ‖zagierEndpointCoordinate (δ t)‖ < 1 / 9 := by
    change ‖zagierEndpointCoordinate (zagierEndpointCirclePath r hr t)‖ < 1 / 9
    rw [zagierEndpointCirclePath_coordinate, norm_complexCirclePath, abs_of_pos hr.1]
    exact hr.2
  have hS : AnalyticContinuationAlong δ (fun _ => zagierEndpointSolution) :=
    analyticContinuationAlong_zagierEndpointSolution_circle r hr
  have hSE (t : I) : zagierSecondOrderODE zagierEndpointSolution =ᶠ[𝓝 (δ t)] 0 := by
    filter_upwards [eventually_ne_nhds (h₁ t),
      (analyticAt_zagierEndpointCoordinate (h₁ t)).continuousAt.norm.eventually_lt_const (hnorm t)]
      with z hz htz
    exact zagierEndpointSolution_ode hz htz
  let γ := zagierMobiusPath δ h₁ hreg
  let k : ℂ := c * (2 * Real.pi * Complex.I)
  have hk : k ≠ 0 := mul_ne_zero hc (mul_ne_zero
    (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  have hf₀' : f 0 =ᶠ[𝓝 (q : ℂ)] zagierAnalytic := by simpa only [he] using hf₀
  have hf₁' : f 1 =ᶠ[𝓝 (q : ℂ)] fun z => zagierAnalytic z + k * zagierEndpointSolution z := by
    simpa only [he, k] using hf₁
  obtain ⟨hq₀, hq₁, hq₂⟩ := zagierEndpointInterval_noncritical hq
  refine ⟨q, hq, r, hr, hrR.trans_le (min_le_left R S), rfl, γ, fun _ => rfl, k, hk, ?_⟩
  intro φ ψ hφ hψ
  constructor
  · apply Subtype.ext
    apply mobiusGermPullback_injective hq₀ hq₁ hq₂
    have ht := mobiusGermPullback_zagierPathTransport b δ h₁ hreg hq₁ hq₁ hf hE h₀ h₂ φ
      (hφ.trans (Germ.coe_eq.mpr hf₀'.symm))
    rw [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, hφ, hψ]
    exact ht.trans (Germ.coe_eq.mpr hf₁')
  · apply Subtype.ext
    apply mobiusGermPullback_injective hq₀ hq₁ hq₂
    exact (mobiusGermPullback_zagierPathTransport b δ h₁ hreg hq₁ hq₁ hS hSE h₀ h₂ ψ hψ).trans
      hψ.symm

theorem exists_zagierEndpoint_endpointCircle_transport_shear (b : zagierODERegularSet) :
    ∃ q : ℝ, ∃ hq : q ∈ Ioo 0 (1 / 9 : ℝ), ∃ r : ℝ, ∃ hr : r ∈ Ioo 0 (1 / 9 : ℝ),
      q = (1 - 9 * r) / (9 * (1 - r)) ∧
      ∃ γ : Path (⟨mobiusCoordinate q, mobiusCoordinate_regular_of_mem_Ioo hq⟩ : zagierODERegularSet)
        ⟨mobiusCoordinate q, mobiusCoordinate_regular_of_mem_Ioo hq⟩,
      (∀ t, (γ t : ℂ) = mobiusCoordinate (zagierEndpointCirclePath r hr t)) ∧
      ∃ k : ℂ, k ≠ 0 ∧ ∀ φ ψ : zagierSolutionGerms (mobiusCoordinate q),
        mobiusGermPullback (zagierEndpointInterval_noncritical hq).2.1
          (φ : Germ (𝓝 (mobiusCoordinate q)) ℂ) = zagierAnalytic →
        mobiusGermPullback (zagierEndpointInterval_noncritical hq).2.1
          (ψ : Germ (𝓝 (mobiusCoordinate q)) ℂ) = zagierEndpointSolution →
        zagierPathTransport b γ φ = φ + k • ψ ∧ zagierPathTransport b γ ψ = ψ := by
  obtain ⟨q, hq, r, hr, _, hqr, γ, hγ, k, hk, hshear⟩ :=
    exists_zagierEndpoint_endpointCircle_transport_shear_lt b (R := 1) (by norm_num)
  exact ⟨q, hq, r, hr, hqr, γ, hγ, k, hk, hshear⟩

theorem exists_zagierEndpoint_commonBase_transport_shears {r : ℝ}
    (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) (φ ψ : zagierSolutionGerms (mobiusCoordinate r))
    (hφ : mobiusGermPullback (zagierEndpointInterval_noncritical hr).2.1
      (φ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = zagierAnalytic)
    (hψ : mobiusGermPullback (zagierEndpointInterval_noncritical hr).2.1
      (ψ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = zagierEndpointSolution) :
    let b : zagierODERegularSet := ⟨mobiusCoordinate r, mobiusCoordinate_regular_of_mem_Ioo hr⟩
    ∃ γ δ : Path b b, ∃ k l : ℂ, k ≠ 0 ∧ l ≠ 0 ∧
      zagierPathTransport b γ φ = φ ∧ zagierPathTransport b γ ψ = ψ + k • φ ∧
      zagierPathTransport b δ φ = φ + l • ψ ∧ zagierPathTransport b δ ψ = ψ := by
  let b : zagierODERegularSet := ⟨mobiusCoordinate r, mobiusCoordinate_regular_of_mem_Ioo hr⟩
  obtain ⟨s, hs, γ, _, k, hk, hγ⟩ := exists_zagierEndpoint_circle_transport_shear b
  obtain ⟨t, ht, _, _, _, δ, _, l, hl, hδ⟩ :=
    exists_zagierEndpoint_endpointCircle_transport_shear b
  let η := zagierEndpointPath hr hs
  let θ := zagierEndpointPath hr ht
  have hH (u : ℝ) (hu : u ∈ Ioo 0 (1 / 9 : ℝ)) : AnalyticAt ℂ zagierAnalytic (u : ℂ) :=
    (zagierEndpointInterval_solutions hu).1
  have hHE (u : ℝ) (hu : u ∈ Ioo 0 (1 / 9 : ℝ)) :
      zagierSecondOrderODE zagierAnalytic =ᶠ[𝓝 (u : ℂ)] 0 :=
    (zagierEndpointInterval_solutions hu).2.1
  have hS (u : ℝ) (hu : u ∈ Ioo 0 (1 / 9 : ℝ)) :
      AnalyticAt ℂ zagierEndpointSolution (u : ℂ) :=
    (zagierEndpointInterval_solutions hu).2.2.1
  have hSE (u : ℝ) (hu : u ∈ Ioo 0 (1 / 9 : ℝ)) :
      zagierSecondOrderODE zagierEndpointSolution =ᶠ[𝓝 (u : ℂ)] 0 :=
    (zagierEndpointInterval_solutions hu).2.2.2
  obtain ⟨hγφ, hγψ⟩ := hγ (zagierPathTransport b η φ) (zagierPathTransport b η ψ)
    (mobiusGermPullback_zagierEndpointPath b hr hs hH hHE φ hφ)
    (mobiusGermPullback_zagierEndpointPath b hr hs hS hSE ψ hψ)
  obtain ⟨hδφ, hδψ⟩ := hδ (zagierPathTransport b θ φ) (zagierPathTransport b θ ψ)
    (mobiusGermPullback_zagierEndpointPath b hr ht hH hHE φ hφ)
    (mobiusGermPullback_zagierEndpointPath b hr ht hS hSE ψ hψ)
  refine ⟨(η.trans γ).trans η.symm, (θ.trans δ).trans θ.symm, k, l, hk, hl, ?_, ?_, ?_, ?_⟩
  · rw [zagierPathTransport_trans, zagierPathTransport_trans, hγφ, zagierPathTransport_symm]
  · rw [zagierPathTransport_trans, zagierPathTransport_trans, hγψ,
      zagierPathTransport_add, zagierPathTransport_smul,
      zagierPathTransport_symm, zagierPathTransport_symm]
  · rw [zagierPathTransport_trans, zagierPathTransport_trans, hδφ,
      zagierPathTransport_add, zagierPathTransport_smul,
      zagierPathTransport_symm, zagierPathTransport_symm]
  · rw [zagierPathTransport_trans, zagierPathTransport_trans, hδψ, zagierPathTransport_symm]

theorem exists_zagierEndpoint_commonBase_monodromy_shears {r : ℝ}
    (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) :
    let b : zagierODERegularSet := ⟨mobiusCoordinate r, mobiusCoordinate_regular_of_mem_Ioo hr⟩
    ∃ φ ψ : zagierSolutionGerms (mobiusCoordinate r),
      mobiusGermPullback (zagierEndpointInterval_noncritical hr).2.1
        (φ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = zagierAnalytic ∧
      mobiusGermPullback (zagierEndpointInterval_noncritical hr).2.1
        (ψ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = zagierEndpointSolution ∧
      LinearIndependent ℂ ![φ, ψ] ∧ ∃ g h : FundamentalGroup zagierODERegularSet b,
      ∃ k l : ℂ, k ≠ 0 ∧ l ≠ 0 ∧
        zagierMonodromyRepresentation b g φ = φ ∧
        zagierMonodromyRepresentation b g ψ = ψ + k • φ ∧
        zagierMonodromyRepresentation b h φ = φ + l • ψ ∧
        zagierMonodromyRepresentation b h ψ = ψ := by
  obtain ⟨φ, ψ, hφ, hψ, hind⟩ := exists_zagierEndpointSolutionGerms hr
  obtain ⟨γ, δ, k, l, hk, hl, hγφ, hγψ, hδφ, hδψ⟩ :=
    exists_zagierEndpoint_commonBase_transport_shears hr φ ψ hφ hψ
  exact ⟨φ, ψ, hφ, hψ, hind,
    FundamentalGroup.fromPath (X := TopCat.of zagierODERegularSet) ⟦γ⟧,
    FundamentalGroup.fromPath (X := TopCat.of zagierODERegularSet) ⟦δ⟧,
    k, l, hk, hl, hγφ, hγψ, hδφ, hδψ⟩

theorem exists_zagierEndpoint_commonBase_no_common_eigenvector {r : ℝ}
    (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) :
    let p : zagierODERegularSet := ⟨mobiusCoordinate r, mobiusCoordinate_regular_of_mem_Ioo hr⟩
    ∃ φ ψ : zagierSolutionGerms (mobiusCoordinate r), LinearIndependent ℂ ![φ, ψ] ∧
      ∃ g h : FundamentalGroup zagierODERegularSet p, ∀ a b c d : ℂ,
        zagierMonodromyRepresentation p g (a • φ + b • ψ) = c • (a • φ + b • ψ) →
        zagierMonodromyRepresentation p h (a • φ + b • ψ) = d • (a • φ + b • ψ) →
        a = 0 ∧ b = 0 := by
  let p : zagierODERegularSet := ⟨mobiusCoordinate r, mobiusCoordinate_regular_of_mem_Ioo hr⟩
  obtain ⟨φ, ψ, _, _, hind, g, h, k, l, hk, hl, hgφ, hgψ, hhφ, hhψ⟩ :=
    exists_zagierEndpoint_commonBase_monodromy_shears hr
  have hi (a b : ℂ) (he : a • φ + b • ψ = 0) : a = 0 ∧ b = 0 := by
    have hz := Fintype.linearIndependent_iff.mp hind ![a, b] (by
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] using he)
    exact ⟨hz 0, hz 1⟩
  have hi' (a b : ℂ) (he : a • ψ + b • φ = 0) : a = 0 ∧ b = 0 :=
    (hi b a (by simpa only [add_comm] using he)).symm
  refine ⟨φ, ψ, hind, g, h, ?_⟩
  intro a b c d hg hh
  have hb : b = 0 :=
    eq_zero_coefficient_of_linear_shear (zagierMonodromyRepresentation p g) hgφ hgψ hk hi hg
  have ha : a = 0 := eq_zero_coefficient_of_linear_shear
    (zagierMonodromyRepresentation p h) hhψ hhφ hl hi' (a := b) (b := a) (c := d)
    (by simpa only [add_comm] using hh)
  exact ⟨ha, hb⟩

theorem exists_zagierEndpoint_commonBase_orbitSpan {r : ℝ}
    (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) :
    let p : zagierODERegularSet := ⟨mobiusCoordinate r, mobiusCoordinate_regular_of_mem_Ioo hr⟩
    ∃ φ ψ : zagierSolutionGerms (mobiusCoordinate r),
      mobiusGermPullback (zagierEndpointInterval_noncritical hr).2.1
        (φ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = zagierAnalytic ∧
      mobiusGermPullback (zagierEndpointInterval_noncritical hr).2.1
        (ψ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = zagierEndpointSolution ∧
      LinearIndependent ℂ ![φ, ψ] ∧ ∀ a b : ℂ, a ≠ 0 ∨ b ≠ 0 →
        Submodule.span ℂ {φ, ψ} ≤ zagierMonodromyOrbitSpan p (a • φ + b • ψ) := by
  let p : zagierODERegularSet := ⟨mobiusCoordinate r, mobiusCoordinate_regular_of_mem_Ioo hr⟩
  obtain ⟨φ, ψ, hφ, hψ, hind, g, h, k, l, hk, hl, hgφ, hgψ, hhφ, _⟩ :=
    exists_zagierEndpoint_commonBase_monodromy_shears hr
  change zagierMonodromyRepresentation p g φ = φ at hgφ
  change zagierMonodromyRepresentation p g ψ = ψ + k • φ at hgψ
  change zagierMonodromyRepresentation p h φ = φ + l • ψ at hhφ
  refine ⟨φ, ψ, hφ, hψ, hind, ?_⟩
  intro a b hab
  let χ : zagierSolutionGerms (mobiusCoordinate r) := a • φ + b • ψ
  let W := zagierMonodromyOrbitSpan p χ
  change Submodule.span ℂ {φ, ψ} ≤ W
  have hχ : χ ∈ W := self_mem_zagierMonodromyOrbitSpan p χ
  have hinv := (Representation.mem_invtSubmodule (zagierMonodromyRepresentation p)).mp
    (zagierMonodromyOrbitSpan_mem_invtSubmodule p χ)
  have hφW : φ ∈ W := by
    by_cases hb : b = 0
    · have ha : a ≠ 0 := hab.elim id (fun h => False.elim (h hb))
      exact (W.smul_mem_iff ha).mp (by simpa only [χ, hb, zero_smul, add_zero] using hχ)
    · have he : zagierMonodromyRepresentation p g χ - χ = (b * k) • φ := by
        change zagierMonodromyRepresentation p g (a • φ + b • ψ) -
          (a • φ + b • ψ) = (b * k) • φ
        rw [map_add, map_smul, map_smul, hgφ, hgψ]
        simp only [smul_add, mul_smul]
        abel
      have hd := W.sub_mem (hinv g hχ) hχ
      rw [he] at hd
      exact (W.smul_mem_iff (mul_ne_zero hb hk)).mp hd
  have hψW : ψ ∈ W := by
    apply (W.smul_mem_iff hl).mp
    simpa only [hhφ, add_sub_cancel_left] using W.sub_mem (hinv h hφW) hφW
  apply Submodule.span_le.mpr
  intro u hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl
  · exact hφW
  · exact hψW

end DirichletL

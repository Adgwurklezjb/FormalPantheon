import Analysis.FunctionalIndependence

/-!
Formal symmetrization from CDT v2 Section `SympH`, equation `defG`.

This file proves the algebraic substitution invariance of the rational formal
sum. It does not assert descent to an analytic `y`-coordinate.
-/

namespace DirichletL

/-- The rational image of the integer formal Mobius coordinate. -/
noncomputable def mobiusInvolutionQ : PowerSeries ℚ :=
  PowerSeries.map (Int.castRingHom ℚ) mobiusInvolution

theorem constantCoeff_mobiusInvolutionQ :
    PowerSeries.constantCoeff (R := ℚ) mobiusInvolutionQ = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, mobiusInvolutionQ,
    PowerSeries.coeff_map]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_mobiusInvolution, map_zero]

/-- The rational Mobius coordinate is an involution under formal substitution. -/
theorem mobiusInvolutionQ_subst_self :
    MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) mobiusInvolutionQ =
      PowerSeries.X := by
  let w : PowerSeries ℚ := mobiusInvolutionQ
  let u : PowerSeries ℚ := PowerSeries.map (Int.castRingHom ℚ) (oneSubInv 1)
  have hw0 : PowerSeries.constantCoeff (R := ℚ) w = 0 := by
    exact constantCoeff_mobiusInvolutionQ
  have hw : MvPowerSeries.HasSubst (fun (_ : Unit) => w) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hw0)
  have hsub_one : MvPowerSeries.subst (fun (_ : Unit) => w) (1 : PowerSeries ℚ) = 1 := by
    rw [← MvPowerSeries.substAlgHom_apply hw]
    exact map_one _
  have hsub_X : MvPowerSeries.subst (fun (_ : Unit) => w)
      (PowerSeries.X : PowerSeries ℚ) = w := by
    exact MvPowerSeries.subst_X hw ()
  have hu_right : (1 - PowerSeries.X) * u = 1 := by
    simpa [u, pow_one] using congrArg (PowerSeries.map (Int.castRingHom ℚ))
      (oneSubInv_rightInv (k := 1) (by norm_num))
  have hu_left : u * (1 - PowerSeries.X) = 1 := by
    simpa [u, pow_one, mul_comm] using congrArg (PowerSeries.map (Int.castRingHom ℚ))
      (oneSubInv_leftInv (k := 1) (by norm_num))
  have hwu : MvPowerSeries.subst (fun (_ : Unit) => w) u =
      1 - (PowerSeries.X : PowerSeries ℚ) := by
    have hinv : MvPowerSeries.subst (fun (_ : Unit) => w)
          (1 - (PowerSeries.X : PowerSeries ℚ)) *
        MvPowerSeries.subst (fun (_ : Unit) => w) u = 1 := by
      rw [← MvPowerSeries.subst_mul hw]
      rw [hu_right, hsub_one]
    have hsub_one_sub : MvPowerSeries.subst (fun (_ : Unit) => w)
          (1 - (PowerSeries.X : PowerSeries ℚ)) = 1 - w := by
      calc
        MvPowerSeries.subst (fun (_ : Unit) => w)
              (1 - (PowerSeries.X : PowerSeries ℚ)) =
            MvPowerSeries.subst (fun (_ : Unit) => w) 1 -
              MvPowerSeries.subst (fun (_ : Unit) => w) PowerSeries.X := by
                rw [← MvPowerSeries.coe_substAlgHom hw]
                exact (MvPowerSeries.substAlgHom (σ := Unit) (τ := Unit)
                  (R := ℚ) (S := ℚ) hw).map_sub _ _
        _ = 1 - w := by
          calc
            _ = 1 - MvPowerSeries.subst (fun (_ : Unit) => w) PowerSeries.X :=
              congrArg (fun t => t - MvPowerSeries.subst
                (fun (_ : Unit) => w) PowerSeries.X) hsub_one
            _ = 1 - w := congrArg (fun t => 1 - t) hsub_X
    rw [hsub_one_sub] at hinv
    have hrel : 1 - w = u := by
      dsimp [w, mobiusInvolutionQ, mobiusInvolution, u]
      rw [map_neg, map_mul, PowerSeries.map_X]
      calc
        1 - (-(PowerSeries.X * PowerSeries.map (Int.castRingHom ℚ) (oneSubInv 1))) =
            1 + PowerSeries.X * PowerSeries.map (Int.castRingHom ℚ) (oneSubInv 1) := by ring
        _ = (1 - PowerSeries.X) * PowerSeries.map (Int.castRingHom ℚ) (oneSubInv 1) +
            PowerSeries.X * PowerSeries.map (Int.castRingHom ℚ) (oneSubInv 1) := by
          rw [hu_right]
        _ = PowerSeries.map (Int.castRingHom ℚ) (oneSubInv 1) := by ring
    rw [hrel] at hinv
    apply (mul_left_cancel₀ (show u ≠ 0 by
      intro hzero
      rw [hzero, zero_mul] at hu_left
      norm_num at hu_left))
    calc
      u * MvPowerSeries.subst (fun (_ : Unit) => w) u = 1 := hinv
      _ = u * (1 - PowerSeries.X) := hu_left.symm
  have hww : MvPowerSeries.subst (fun (_ : Unit) => w) w =
      -(w * MvPowerSeries.subst (fun (_ : Unit) => w) u) := by
    have hwdef : w = -(PowerSeries.X * u) := by
      dsimp [w, mobiusInvolutionQ, mobiusInvolution, u]
      rw [map_neg, map_mul, PowerSeries.map_X]
    calc
      MvPowerSeries.subst (fun (_ : Unit) => w) w =
          MvPowerSeries.subst (fun (_ : Unit) => w) (-(PowerSeries.X * u)) :=
        congrArg (MvPowerSeries.subst (fun (_ : Unit) => w)) hwdef
      _ = -(w * MvPowerSeries.subst (fun (_ : Unit) => w) u) := by
        rw [← MvPowerSeries.substAlgHom_apply hw]
        simp only [map_neg, map_mul, MvPowerSeries.substAlgHom_X]
        have hXalg : (MvPowerSeries.substAlgHom hw)
            (PowerSeries.X : PowerSeries ℚ) = w := by
          change (MvPowerSeries.substAlgHom hw) (MvPowerSeries.X ()) = w
          exact MvPowerSeries.substAlgHom_X hw ()
        rw [hXalg, MvPowerSeries.substAlgHom_apply]
  rw [hww, hwu]
  rw [show w = -(PowerSeries.X * u) by
    dsimp [w, mobiusInvolutionQ, mobiusInvolution, u]
    rw [map_neg, map_mul, PowerSeries.map_X]]
  rw [show -( -(PowerSeries.X * u) * (1 - PowerSeries.X)) =
      PowerSeries.X * (u * (1 - PowerSeries.X)) by ring]
  rw [hu_left, mul_one]

/-- Formal substitution by the Mobius coordinate fixes the positive symmetrization. -/
theorem subst_mobiusInvolutionQ_symmetrizedFormal (f : PowerSeries ℚ) :
    MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) (symmetrizedFormal f) =
      symmetrizedFormal f := by
  let w : PowerSeries ℚ := mobiusInvolutionQ
  have hw : MvPowerSeries.HasSubst (fun (_ : Unit) => w) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusInvolutionQ)
  have hcomp := MvPowerSeries.subst_comp_subst_apply hw hw f
  change MvPowerSeries.subst (fun (_ : Unit) => w)
      (f + MvPowerSeries.subst (fun (_ : Unit) => w) f) =
    f + MvPowerSeries.subst (fun (_ : Unit) => w) f
  rw [MvPowerSeries.subst_add hw]
  rw [hcomp]
  rw [show (fun (_ : Unit) => MvPowerSeries.subst (fun (_ : Unit) => w) (w)) =
      (fun (_ : Unit) => PowerSeries.X) by
    funext s
    simpa [w] using mobiusInvolutionQ_subst_self]
  have h_id : MvPowerSeries.subst (fun (_ : Unit) => (PowerSeries.X : PowerSeries ℚ)) f = f := by
    simpa [PowerSeries.X] using congrFun
      (MvPowerSeries.subst_self (σ := Unit) (R := ℚ)) f
  rw [h_id]
  simp [symmetrizedFormal, mobiusInvolutionQ, w, add_comm]

theorem coeff_one_mobiusInvolutionQ :
    PowerSeries.coeff (R := ℚ) 1 mobiusInvolutionQ = -1 := by
  simp [mobiusInvolutionQ, mobiusInvolution, PowerSeries.coeff_map,
    PowerSeries.coeff_one_mul, coeff_oneSubInv_of_lt, constantCoeff_oneSubInv]

/-- The positive symmetrization has no linear term in the original coordinate. -/
theorem coeff_one_symmetrizedFormal (f : PowerSeries ℚ) :
    PowerSeries.coeff (R := ℚ) 1 (symmetrizedFormal f) = 0 := by
  change PowerSeries.coeff (R := ℚ) 1
      (f + MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) f) = 0
  rw [map_add, coeff_subst_one constantCoeff_mobiusInvolutionQ,
    coeff_one_mobiusInvolutionQ]
  ring

theorem coeff_two_mobiusInvolutionQ :
    PowerSeries.coeff (R := ℚ) 2 mobiusInvolutionQ = -1 := by
  have hcoeff : PowerSeries.coeff (R := ℤ) 1 (oneSubInv 1) = 1 := by
    have h := congrArg (PowerSeries.coeff (R := ℤ) 1)
      (oneSubInv_rightInv (k := 1) (by norm_num))
    rw [PowerSeries.coeff_one_mul] at h
    simp [PowerSeries.coeff_one_pow, coeff_oneSubInv_of_lt,
      constantCoeff_oneSubInv] at h
    linarith
  simp [mobiusInvolutionQ, mobiusInvolution, PowerSeries.coeff_map,
    PowerSeries.coeff_mul, Finset.Nat.antidiagonal_eq_map, Finset.sum_map,
    Finset.sum_range_succ, coeff_oneSubInv_of_lt, constantCoeff_oneSubInv,
    PowerSeries.coeff_X, hcoeff]

theorem coeff_two_symmetrizedFormal_hA :
    PowerSeries.coeff (R := ℚ) 2 (symmetrizedFormal hA) = 27 := by
  change PowerSeries.coeff (R := ℚ) 2
      (hA + MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) hA) = 27
  rw [map_add, coeff_subst_two constantCoeff_mobiusInvolutionQ,
    coeff_one_mobiusInvolutionQ, coeff_two_mobiusInvolutionQ]
  simp only [hA_coeff_one, hA_coeff_two]
  norm_num

theorem coeff_subst_three {f g : PowerSeries ℚ}
    (hg : PowerSeries.constantCoeff (R := ℚ) g = 0) :
    PowerSeries.coeff (R := ℚ) 3
        (MvPowerSeries.subst (fun (_ : Unit) => g) f) =
      PowerSeries.coeff (R := ℚ) 1 f * PowerSeries.coeff (R := ℚ) 3 g +
        2 * PowerSeries.coeff (R := ℚ) 2 f * PowerSeries.coeff (R := ℚ) 1 g *
          PowerSeries.coeff (R := ℚ) 2 g +
        PowerSeries.coeff (R := ℚ) 3 f * (PowerSeries.coeff (R := ℚ) 1 g) ^ 3 := by
  rw [coeff_subst_eq_sum f g hg 3]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    pow_zero, one_mul, PowerSeries.coeff_one,
    coeff_pow_self_of_constantCoeff_zero g hg]
  simp only [if_neg (by norm_num : ¬(3 : ℕ) = 0)]
  have hpow2 : PowerSeries.coeff (R := ℚ) 3 (g ^ 2) =
      2 * PowerSeries.coeff (R := ℚ) 1 g * PowerSeries.coeff (R := ℚ) 2 g := by
    rw [pow_two, PowerSeries.coeff_mul]
    simp only [Finset.Nat.antidiagonal_eq_map, Finset.sum_map]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
    simp [hg]
    ring
  rw [hpow2]
  ring

theorem coeff_three_mobiusInvolutionQ :
    PowerSeries.coeff (R := ℚ) 3 mobiusInvolutionQ = -1 := by
  have hcoeff : PowerSeries.coeff (R := ℤ) 2 (oneSubInv 1) = 1 := by
    have hcoeff1 : PowerSeries.coeff (R := ℤ) 1 (oneSubInv 1) = 1 := by
      have h1 := congrArg (PowerSeries.coeff (R := ℤ) 1)
        (oneSubInv_rightInv (k := 1) (by norm_num))
      rw [PowerSeries.coeff_one_mul] at h1
      simp [PowerSeries.coeff_one_pow, coeff_oneSubInv_of_lt,
        constantCoeff_oneSubInv] at h1
      linarith
    have h := congrArg (PowerSeries.coeff (R := ℤ) 2)
      (oneSubInv_rightInv (k := 1) (by norm_num))
    rw [PowerSeries.coeff_mul] at h
    simp only [Finset.Nat.antidiagonal_eq_map, Finset.sum_map] at h
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at h
    simp [Finset.Nat.antidiagonal_eq_map, Finset.sum_map,
      PowerSeries.coeff_one_pow, coeff_oneSubInv_of_lt,
      constantCoeff_oneSubInv, PowerSeries.coeff_X] at h
    linarith
  simp [mobiusInvolutionQ, mobiusInvolution, PowerSeries.coeff_map,
    PowerSeries.coeff_mul, Finset.Nat.antidiagonal_eq_map, Finset.sum_map,
    Finset.sum_range_succ, coeff_oneSubInv_of_lt, constantCoeff_oneSubInv,
    PowerSeries.coeff_X, hcoeff]

theorem coeff_three_symmetrizedFormal_hA :
    PowerSeries.coeff (R := ℚ) 3 (symmetrizedFormal hA) = 27 := by
  change PowerSeries.coeff (R := ℚ) 3
      (hA + MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) hA) = 27
  rw [map_add, coeff_subst_three constantCoeff_mobiusInvolutionQ,
    coeff_one_mobiusInvolutionQ, coeff_two_mobiusInvolutionQ,
    coeff_three_mobiusInvolutionQ]
  simp only [hA_coeff_one, hA_coeff_two]
  have hA3 : PowerSeries.coeff (R := ℚ) 3 hA = 93 := by
    simp [hA, zagierGenerating, generatingSeries, zagierC_three]
  rw [hA3]
  norm_num

/-- The invariant coordinate in CDT's symmetrization is `X + w_Q`. -/
noncomputable def mobiusCoordinateQ : PowerSeries ℚ :=
  PowerSeries.X + mobiusInvolutionQ

theorem mobiusCoordinateQ_eq :
    mobiusCoordinateQ = -(PowerSeries.X ^ 2 *
      PowerSeries.map (Int.castRingHom ℚ) (oneSubInv 1)) := by
  dsimp [mobiusCoordinateQ, mobiusInvolutionQ, mobiusInvolution]
  rw [map_neg, map_mul, PowerSeries.map_X]
  have hu : (1 - (PowerSeries.X : PowerSeries ℚ)) *
      PowerSeries.map (Int.castRingHom ℚ) (oneSubInv 1) = 1 := by
    simpa [pow_one] using congrArg (PowerSeries.map (Int.castRingHom ℚ))
      (oneSubInv_rightInv (k := 1) (by norm_num))
  have hrel : 1 - PowerSeries.map (Int.castRingHom ℚ) (oneSubInv 1) =
      -(PowerSeries.X * PowerSeries.map (Int.castRingHom ℚ) (oneSubInv 1)) := by
    rw [show 1 = (1 - (PowerSeries.X : PowerSeries ℚ)) *
        PowerSeries.map (Int.castRingHom ℚ) (oneSubInv 1) by exact hu.symm]
    ring
  calc
    PowerSeries.X + -(PowerSeries.X *
        PowerSeries.map (Int.castRingHom ℚ) (oneSubInv 1)) =
      PowerSeries.X * (1 - PowerSeries.map (Int.castRingHom ℚ) (oneSubInv 1)) := by ring
    _ = PowerSeries.X * (-(PowerSeries.X *
        PowerSeries.map (Int.castRingHom ℚ) (oneSubInv 1))) := by rw [hrel]
    _ = -(PowerSeries.X ^ 2 *
        PowerSeries.map (Int.castRingHom ℚ) (oneSubInv 1)) := by ring

theorem subst_mobiusCoordinateQ :
    MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) mobiusCoordinateQ =
      mobiusCoordinateQ := by
  let w : PowerSeries ℚ := mobiusInvolutionQ
  have hw : MvPowerSeries.HasSubst (fun (_ : Unit) => w) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusInvolutionQ)
  change MvPowerSeries.subst (fun (_ : Unit) => w)
      (PowerSeries.X + w) = PowerSeries.X + w
  rw [MvPowerSeries.subst_add hw]
  have hX : MvPowerSeries.subst (fun (_ : Unit) => w)
      (PowerSeries.X : PowerSeries ℚ) = w := MvPowerSeries.subst_X hw ()
  rw [hX, mobiusInvolutionQ_subst_self]
  ring

theorem constantCoeff_symmetrizedFormal (f : PowerSeries ℚ) :
    PowerSeries.constantCoeff (R := ℚ) (symmetrizedFormal f) =
      2 * PowerSeries.constantCoeff (R := ℚ) f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  change PowerSeries.coeff (R := ℚ) 0
      (f + MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) f) = _
  rw [map_add, coeff_subst_zero constantCoeff_mobiusInvolutionQ]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  ring

theorem coeff_two_symmetrizedFormal (f : PowerSeries ℚ) :
    PowerSeries.coeff (R := ℚ) 2 (symmetrizedFormal f) =
      2 * PowerSeries.coeff (R := ℚ) 2 f - PowerSeries.coeff (R := ℚ) 1 f := by
  change PowerSeries.coeff (R := ℚ) 2
      (f + MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) f) = _
  rw [map_add, coeff_subst_two constantCoeff_mobiusInvolutionQ,
    coeff_one_mobiusInvolutionQ, coeff_two_mobiusInvolutionQ]
  ring

theorem constantCoeff_mobiusCoordinateQ :
    PowerSeries.constantCoeff (R := ℚ) mobiusCoordinateQ = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, mobiusCoordinateQ]
  simp [constantCoeff_mobiusInvolutionQ]

theorem coeff_one_mobiusCoordinateQ :
    PowerSeries.coeff (R := ℚ) 1 mobiusCoordinateQ = 0 := by
  rw [mobiusCoordinateQ, map_add, coeff_one_mobiusInvolutionQ]
  simp [PowerSeries.coeff_X]

theorem coeff_two_mobiusCoordinateQ :
    PowerSeries.coeff (R := ℚ) 2 mobiusCoordinateQ = -1 := by
  rw [mobiusCoordinateQ, map_add, coeff_two_mobiusInvolutionQ]
  simp [PowerSeries.coeff_X]

theorem coeff_three_mobiusCoordinateQ :
    PowerSeries.coeff (R := ℚ) 3 mobiusCoordinateQ = -1 := by
  rw [mobiusCoordinateQ, map_add, coeff_three_mobiusInvolutionQ]
  simp [PowerSeries.coeff_X]

end DirichletL

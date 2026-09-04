# Proposed analytic contract for the conditional H₁ ≤ 236 spine

This document freezes a proposed architecture; it does not introduce a Lean assumption and does not claim H₁ ≤ 236 unconditionally. No `AnalyticInput.lean` file should be created until the blockers under “Statement-freeze failures” have been resolved by human mathematical review.

## Logical layers and proposed modules

| Layer | Proposed module | Responsibility |
|---|---|---|
| 1 | `BoundedGaps.H1236.Analytic.Support` | slice data, `T_k`, relevant modulus cells, `I/J/K` domains |
| 2 | `BoundedGaps.H1236.Analytic.DistributionDefinitions` | coefficient sequences, scales, Siegel–Walfisz, Type I/II/III classes, equidistribution |
| 3 | `BoundedGaps.H1236.Analytic.ModifiedSieve` | universal form of Stadlmann Proposition 1 |
| 4 | `BoundedGaps.H1236.Analytic.TypeI`, `TypeII`, `TypeIII`, `NegativeOmega` | classical and extended distribution estimates |
| 5 | `BoundedGaps.H1236.Analytic.HarmanMinorant` | Proposition 2, roughness, mass, pointwise bounds, `c₁,c₂` |
| 6 | `BoundedGaps.H1236.Certificates.Support` | 105 support-cell checks and sound rational checkers |
| 7 | `BoundedGaps.H1236.TrialFunction` and `Certificates.Integrals` | exact `F`, regularity, `I/J/K`, strict crossing at positive enlargement |
| 8 | eventual `BoundedGaps.H1236.AnalyticInput` | a universal bundle of Propositions 1–3 only, after statement approval |
| 9 | `BoundedGaps.H1236.ConditionalMain` | instantiate the universal bundle and finite certificates at `k=48` |
| 10 | existing `TupleBridge` and `Statement` | prime shifts → explicit gap statement → liminf statement |

Imports must point down this table. In particular, analytic modules must not import `Tuple48`, and the future analytic-input structure must not mention the desired 48-tuple conclusion.

## Exact numerical data

The proposed declarations, initially in `Parameters`, are:

```lean
def h1236K : ℕ := 48
def h1236Delta : ℚ := 7 / 500
def h1236A1 : ℚ := 253 / 1000
def h1236A2 : ℚ := 129 / 500
def h1236Xi1 : ℚ := 759 / 2000
def h1236Xi2 : ℚ := 4021 / 10000
def h1236Xi3 : ℚ := 4021 / 10000
def h1236Eta : ℚ := 1 / 10000000000
def h1236Beta : ℚ := 979 / 5000
def h1236C2 : ℚ := 24
def h1236C1Upper : ℚ :=
  1291475390625 / 14389093733134384
```

The cap functions are total so the plateau convention is explicit:

```lean
def h1236LowerCap : ℕ → ℚ
  | 0 => 0
  | 1 => 39 / 250
  | 2 => 39 / 250
  | 3 => 17 / 100
  | 4 => 23 / 125
  | 5 => 19 / 100
  | _ => 101 / 500

def h1236UpperCap : ℕ → ℚ
  | 0 => 0
  | 1 => 153 / 1000
  | 2 => 153 / 1000
  | 3 => 167 / 1000
  | 4 => 181 / 1000
  | _ => 19 / 100
```

No numerical value is assigned to the positive support enlargement `ε_s`. The supplied certificates are at `ε_s=0`, and the supplied sources prove only an informal existential passage to some positive value.

## Core support types

The following is a complete proposed interface. `maxCount_spec` avoids making the structure depend on a particular API for `floor`.

```lean
structure SupportSliceData (k slices : ℕ) where
  delta : ℝ
  epsilon : ℝ
  A : Fin (slices + 1) → ℝ
  B : Fin slices → ℕ → ℝ
  maxCount : ℕ
  slices_pos : 0 < slices
  delta_pos : 0 < delta
  epsilon_pos : 0 < epsilon
  A_zero : A 0 = -epsilon
  A_strict : StrictMono A
  A_last_lt : A (Fin.last slices) < 1 / 2 - epsilon
  maxCount_spec :
    (maxCount : ℝ) ≤ 1 / delta ∧ 1 / delta < (maxCount + 1 : ℕ)
  cap_pos : ∀ j m, 1 ≤ m → m ≤ maxCount → delta < B j m
  cap_mono : ∀ j m, 1 ≤ m → m < maxCount → B j m ≤ B j (m + 1)
  cap_step : ∀ j m, 1 ≤ m → m < maxCount → B j (m + 1) ≤ B j m + delta
```

For `t : Fin k → ℝ`, define

```lean
def inUnitCube (t : Fin k → ℝ) : Prop :=
  ∀ i, 0 ≤ t i ∧ t i ≤ 1

def supportTotal (t : Fin k → ℝ) : ℝ := ∑ i, t i

def largeCoordinates (P : SupportSliceData k slices)
    (t : Fin k → ℝ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => P.delta < t i)

def supportLargeMass (P : SupportSliceData k slices)
    (t : Fin k → ℝ) : ℝ :=
  ∑ i ∈ largeCoordinates P t, t i

def supportRegion (P : SupportSliceData k slices) : Set (Fin k → ℝ) :=
  {t | inUnitCube t ∧ ∃ j : Fin slices,
    P.A j.castSucc + P.epsilon ≤ supportTotal t ∧
    supportTotal t < P.A j.succ + P.epsilon ∧
    supportLargeMass P t ≤ P.B j (largeCoordinates P t).card}
```

The fixed two-slice data at a supplied `ε_s>0` has
`A=(-ε_s,253/1000,129/500)` and the two cap functions above. A separate `limitingSupportRegion` uses `ε_s=0` and the two disjoint bands
`S≤253/1000` and `253/1000<S≤129/500`; it is not a value of `SupportSliceData`, because that structure deliberately requires positive enlargement.

```lean
def h1236SupportData (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon < 121 / 500) :
    SupportSliceData 48 2

def limitingSupportRegion : Set (Fin 48 → ℝ) :=
  {t | inUnitCube t ∧
    ((supportTotal t ≤ 253 / 1000 ∧
        supportLargeMassAt (7 / 500) t ≤
          h1236LowerCap (largeCoordinatesAt (7 / 500) t).card) ∨
      (253 / 1000 < supportTotal t ∧ supportTotal t ≤ 129 / 500 ∧
        supportLargeMassAt (7 / 500) t ≤
          h1236UpperCap (largeCoordinatesAt (7 / 500) t).card))}
```

The bound `epsilon<121/500` is exactly `A₂<1/2-epsilon`. The support data must prove the cap conditions rather than store them as unchecked facts.

## Relevant moduli and equidistribution

Use a natural scale `x : ℕ` in Lean. This makes every sum finite and aligns with existing FormalPantheon asymptotics. The manuscript’s real `x` requires a proved floor/ceiling and dyadic adapter; it must not be hidden in notation.

Define

```lean
def logBaseNat (x n : ℕ) : ℝ := Real.log (n : ℝ) / Real.log (x : ℝ)

def IsSmoothAt (x : ℕ) (delta : ℝ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) < Real.rpow (x : ℝ) delta
```

For `j,j' : Fin slices`, `m,m' : ℕ`, and `q : ℕ`, `RelevantModulusCell P x ε₀ j j' m m' q` means that there exist `e e' : ℕ`, `f : Fin m → ℕ`, and `f' : Fin m' → ℕ` such that all of the following hold:

1. `q=e*e'*(∏i,f i)*(∏i,f' i)` and `1≤q≤x`;
2. `1≤e,e'≤x`, every `1≤f i≤x`, and every `1≤f' i≤x`;
3. `logBaseNat x (∏i,f i)≤(1-ε₀)*P.B j m`;
4. `logBaseNat x (∏i,f' i)≤(1-ε₀)*P.B j' m'`;
5. `logBaseNat x (e*(∏i,f i))≤(1-ε₀)*(P.A j.succ-P.epsilon)`;
6. `logBaseNat x (e'*(∏i,f' i))≤(1-ε₀)*(P.A j'.succ+P.epsilon)`;
7. `IsSmoothAt x P.delta (e*e')`;
8. `P.delta≤logBaseNat x (f i)` and `P.delta≤logBaseNat x (f' i)` for every index;
9. `m≤P.maxCount` and `m'≤P.maxCount`.

The asymmetry in items 5–6 is copied from Definition 2. It requires human confirmation, but is not normalized away here.

```lean
def relevantModuli (P : SupportSliceData k slices)
    (x : ℕ) (epsilon0 : ℝ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun q =>
    ∃ j j' m m', RelevantModulusCell P x epsilon0 j j' m m' q)
```

For `f : ℕ → ℕ → ℂ`, set

```lean
def progressionError (f : ℕ → ℕ → ℂ)
    (x q : ℕ) (a : ℤ) : ℝ :=
  ‖(∑ n ∈ Finset.Icc x (2 * x),
      if (n : ℤ) % q = a % q then f n x else 0) -
    ((Nat.totient q : ℂ)⁻¹ *
      ∑ n ∈ Finset.Icc x (2 * x),
        if Nat.Coprime n q then f n x else 0)‖
```

The proposed exact property is:

```lean
def EquidistributedForRelevantModuli
    (P : SupportSliceData k slices) (f : ℕ → ℕ → ℂ) : Prop :=
  ∀ power : ℝ, 0 < power →
  ∀ epsilon0 : ℝ, 0 < epsilon0 → epsilon0 < 1 →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X0 : ℕ, 3 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
      ∀ a : ℤ,
        (∀ p : ℕ, p.Prime → p ≤ x → Int.gcd a p = 1) →
          (∑ q ∈ (relevantModuli P x epsilon0).filter Squarefree,
            progressionError f x q a) ≤
              C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) power
```

`RealEquidistributedForRelevantModuli P ρ` abbreviates this property for `fun n x => (ρ n x : ℂ)`.

Fixed parameters: `P`, `f`, and `power,ε₀` after their universal introduction. Uniformly varying parameters: `x,a,q,j,j',m,m'`. `C` and `X₀` may depend on `P,f,power,ε₀`, but not on a varying parameter.

## Minorant contract

The family has the complete signature

```lean
abbrev MinorantFamily := ℕ → ℕ → ℝ
```

with these proposed predicates:

```lean
def primeIndicatorReal (n : ℕ) : ℝ := if n.Prime then 1 else 0

def IsPrimeMinorant (rho : MinorantFamily) (c2 : ℝ) : Prop :=
  0 ≤ c2 ∧ ∀ᶠ x : ℕ in Filter.atTop,
    ∀ n ∈ Finset.Icc x (2 * x),
      -c2 ≤ rho n x ∧ rho n x ≤ primeIndicatorReal n

def HasRoughSupport (rho : MinorantFamily) (beta : ℝ) : Prop :=
  ∀ᶠ x : ℕ in Filter.atTop,
    ∀ n ∈ Finset.Icc x (2 * x), rho n x ≠ 0 →
      ∀ p : ℕ, p.Prime → p ∣ n →
        Real.rpow (x : ℝ) beta < (p : ℝ)

def HasMinorantMass (rho : MinorantFamily) (c1 : ℝ) : Prop :=
  Filter.Tendsto
    (fun x : ℕ =>
      (∑ n ∈ Finset.Icc x (2 * x), rho n x) *
        Real.log (x : ℝ) / (x : ℝ))
    Filter.atTop (nhds (1 - c1))

def BetaExceedsOneCaps
    (P : SupportSliceData k slices) (beta : ℝ) : Prop :=
  ∀ j : Fin slices, P.B j 1 < beta
```

`HarmanParameterConditions ξ₁ ξ₂ ξ₃` is exactly
`ξ_i∈(0,1)`, `2ξ₁+3ξ₂<2`, `ξ₂≤ξ₃`, `ξ₁+9ξ₂<4`, `2ξ₁+ξ₂>1`, and `17ξ₂<7`.

`harmanLoss ξ₂` is the sum of the two fully specified integrals in source-ledger entry L-P02. `harmanMinorantFormula ξ₂ n x` is `1_P(n)-Γ_A(n;x)-Γ_B(n;x)` with exactly the factorization regions in L-P02. The specification is:

```lean
structure HarmanMinorantSpec
    (P : SupportSliceData k slices)
    (xi1 xi2 xi3 : ℝ) (rho : MinorantFamily)
    (c1 c2 beta : ℝ) : Prop where
  formula : ∀ n x, rho n x = harmanMinorantFormula xi2 n x
  beta_eq : beta = 1 - 2 * xi2
  c1_eq : c1 = harmanLoss xi2
  c2_eq : c2 = if 4 / 10 < xi2 then 24 else 0
  pointwise : IsPrimeMinorant rho c2
  distributed : RealEquidistributedForRelevantModuli P rho
  rough : HasRoughSupport rho beta
  mass : HasMinorantMass rho c1
```

The source uses `x∈ℝ` and primes represented by exponents `p=x^α`. To implement the natural-scale formula above, `HarmanFactorRegion` must be introduced in `HarmanMinorant.lean` as a finite predicate on ordered prime factorizations, using inequalities between `Real.log p / Real.log x` and the exact endpoints. This is the exact missing definition; without it, `harmanMinorantFormula` cannot yet be typechecked.

## Trial function and functionals

```lean
def CoordinateSymmetric (F : (Fin k → ℝ) → ℝ) : Prop :=
  ∀ sigma : Equiv.Perm (Fin k), ∀ t,
    F (fun i => t (sigma i)) = F t

def SupportedOn
    (P : SupportSliceData k slices)
    (F : (Fin k → ℝ) → ℝ) : Prop :=
  ∀ t, t ∉ supportRegion P → F t = 0
```

After `modifiedI`, `modifiedJ`, and the corrected coordinatewise `modifiedKAt`
are defined, the regularity bundle is:

```lean
structure ModifiedTrialAdmissible
    (P : SupportSliceData k slices)
    (F : (Fin k → ℝ) → ℝ) : Prop where
  symmetric : CoordinateSymmetric F
  measurable : Measurable F
  supported : SupportedOn P F
  square_integrable :
    MeasureTheory.IntegrableOn (fun t => F t ^ 2) (maynardCube k)
  J_integrable : ModifiedJIntegrable P F
  K_integrable : ∀ i : Fin k, ModifiedKIntegrable P i F
```

The mathematical definitions to encode are:

```lean
noncomputable def modifiedI
    (P : SupportSliceData k slices)
    (F : (Fin k → ℝ) → ℝ) : ℝ

noncomputable def modifiedJ
    (P : SupportSliceData k slices)
    (F : (Fin k → ℝ) → ℝ) : ℝ

def ModifiedJIntegrable
    (P : SupportSliceData k slices)
    (F : (Fin k → ℝ) → ℝ) : Prop

def ModifiedKIntegrable
    (P : SupportSliceData k slices) (i : Fin k)
    (F : (Fin k → ℝ) → ℝ) : Prop
```

\[
I_P(F)=\int_{T(P)}F(t)^2\,dt,
\]

\[
J_P(F)=\sum_{r,r'}\int
1_{s\le\max(A_r-\varepsilon_s,A_{r'}-\varepsilon_s)}
1_{s+u\in[A_{r-1}+\varepsilon_s,A_r+\varepsilon_s]}
1_{s+v\in[A_{r'-1}+\varepsilon_s,A_{r'}+\varepsilon_s]}
F(t,u)F(t,v)\,dt\,du\,dv,
\]
where `s` is the sum of the `k-1` common coordinates.

Milestone 3C resolved the printed `K` defect from Lemma 1 and the proof of
Proposition 1; see `K_FUNCTIONAL_RESOLUTION.md`. For a distinguished
coordinate `i`, put `s_i(t)=sum_(j != i) t_j`. The source-forced definition is

\[
K_{P,i}(F)=\sum_{r,r'}\int_{[0,1]^k}
1_{s_i(t)>\max(A_r-\varepsilon_s,A_{r'}-\varepsilon_s)}
1_{\sum_jt_j\in[A_{r-1}+\varepsilon_s,A_r+\varepsilon_s]}
1_{\sum_jt_j\in[A_{r'-1}+\varepsilon_s,A_{r'}+\varepsilon_s]}
F(t)^2\,dt.
\]

The correction is to replace the free `t'_k` in Definition 5's third domain
condition by the already integrated `t_k`; no second last-coordinate
integration is added. Equivalently, the same total point must lie in both
indicated bands. The double sum reduces, modulo null band boundaries, to

\[
K_{P,i}(F)=\sum_r\int_{[0,1]^k}
1_{s_i(t)>A_r-\varepsilon_s}
1_{\sum_jt_j\in[A_{r-1}+\varepsilon_s,A_r+\varepsilon_s]}
F(t)^2\,dt.
\]

The implementation interface keeps the coordinate explicit:

```lean
def modifiedKRegion
    (P : SupportSliceData k slices) (i : Fin k)
    (r r' : Fin slices) : Set (Fin k → ℝ)

noncomputable def modifiedKAt
    (P : SupportSliceData k slices) (i : Fin k)
    (F : (Fin k → ℝ) → ℝ) : ℝ
```

`modifiedKRegion` must encode exactly the three indicators above.
`CoordinateSymmetric F` implies that `modifiedKAt P i F` is independent of
`i`, and hence that its sum over coordinates is `k` times any one value. The
body and the integrability predicate are now statement-ready; their
measure-theoretic proofs remain obligations.

With the formula fixed by the source reconstruction, the strict criterion is
exactly:

```lean
def HasStrictModifiedSieveRatio
    (P : SupportSliceData k slices)
    (i : Fin k) (F : (Fin k → ℝ) → ℝ) (c1 c2 : ℝ) : Prop :=
  0 < modifiedI P F ∧
    modifiedI P F <
      k * (1 - c1) * modifiedJ P F - k * c2 * modifiedKAt P i F
```

For a trial function in `ModifiedTrialAdmissible`, this denominator-cleared
form is independent of `i` and is equivalent to the source quotient because
positivity of `I` is explicit.

The fixed trial-witness surface has complete signatures

```lean
def h1236Profile (ell : Fin 3) (t : ℝ) : ℝ

def h1236TrialFunction (t : Fin 48 → ℝ) : ℝ

theorem h1236TrialFunction_formula (t : Fin 48 → ℝ) :
    h1236TrialFunction t =
      limitingSupportIndicator t *
        (∑ ell : Fin 3,
          h1236TrialCoefficient ell *
            ∏ i : Fin 48, h1236Profile ell (t i))
```

`h1236Profile` is defined from the 3×9 and 3×13 exact rational coefficient arrays printed in the dossier, using degree-8 Chebyshev evaluation on `[0,7/500]`, degree-12 evaluation on `(7/500,101/500]`, and zero elsewhere. `h1236TrialCoefficient` is exactly `(571087/10⁹,-12804621/125000000,1)`. `limitingSupportIndicator` is the real-valued indicator of the two disjoint limiting bands specified above; these are data definitions, not externally asserted numerical facts.

## Proposition 3 predicates

For a cell pair, define `ω=(A_j+A_j')/2-1/4` and `XiCell P j j' m m' y` by `y_i∈[δ,1]` and the two cap sums. `IsPartition loads caps` means the bins are pairwise disjoint, their union is every index, and each bin sum is at most its matching capacity.

`Prop3Global P ξ₁ ξ₂ ξ₃ η` is the conjunction:

1. `min(ξ₁-4A_last+2/3,1/7-(34/7)A_last)-2η>δ`;
2. `2-36A_last-13δ+100η≥0`;
3. `min(ξ₂/10-(32/10)A_last+8/10,ξ₂/4+11/16-3A_last)-2η≥δ`;
4. `11/8-(7/2)A_last-(9/8)ξ₃-2η>δ`.

`Prop3FiniteLocalNonnegative P ξ₁ ξ₂ ξ₃ η` universally quantifies `j,j',0≤m,m'≤maxCount` with `m+m'>0` and every `y` in the cell, and requires:

1. a two-bin partition with caps `ξ₁-2η`, `1/6-4ω-2η`;
2. a two-bin partition with caps `2/5+(24/5)ω+(7/5)δ-2η`, `1/14-(24/7)ω-2η`;
3. a three-bin partition with caps `1/3+8ω+(7/3)δ-4η`, `1/10-(34/5)ω-(7/5)δ-4η`, `1/35+(22/35)ω+(21/35)δ-4η`;
4. for every `0≤ω₀≤ω` and `ξ₂-η≤γ≤1/3+8ω+(7/3)δ+3η`, a four-bin partition with caps `γ-2δ-8ω₀-η`, `1/2-γ-2ω₀-η`, `δ+4ω₀-η`, `8ω₀`;
5. a two-bin partition with caps `1-6ω-(3/2)ξ₃-2η`, `(5/2)ω+(3/8)ξ₃-2η`.

At `ω₀=0`, item 4 is retained and its fourth bin is empty. The negative range is not included in this finite predicate.

## Exact negative-ω₀ obligation

Milestone 3E resolves the Lemma 6 divisor loss as `52ε_d`, not 100. With
a general third-range loss `Lε_d`, Lemma 13 gives near-zero capacities

```text
γ - 2δ - 8ω₀ - (L+6)ε_d
1/2 - γ - 2ω₀ - 6ε_d
δ + 4ω₀ + 9ε_d
8ω₀ + (L+3)ε_d.
```

The source-valid choice `L=52` therefore requires `58ε_d≤η` and has
fourth capacity `8ω₀+55ε_d`. The complete loss calculation and the
`52/100` version audit are in `NEGATIVE_OMEGA_SOURCE_RESOLUTION.md`.

The corrected analytic theorem ultimately needs this property:

```lean
def NegativeOmegaDistribution
    (P : SupportSliceData k slices)
    (xi2 eta : ℝ) : Prop :=
  ∀ f : ℕ → ℕ → ℂ, GeneratedMinorantTypeII P xi2 eta f →
  ∀ j j' m m', m ≤ P.maxCount → m' ≤ P.maxCount →
  ∀ omega0 gamma : ℝ,
    -eta ≤ omega0 → omega0 < 0 →
    xi2 - eta ≤ gamma →
    gamma ≤ 1 / 3 + 8 * cellOmega P j j' +
      7 * P.delta / 3 + 3 * eta →
    EquidistributedOnCell P f j j' m m'
```

Here `GeneratedMinorantTypeII` is not the broad Type-II clause printed in
Definition 9. It must be a proved generated class exposing every Buchstab,
Heath--Brown, sifted, and direct term used by Proposition 2, together with a
uniform interval-Siegel--Walfisz certificate for one grouped factor.
`EquidistributedOnCell` is L-S03 restricted to one cell and to the dyadic
moduli `q≍x^(1/2+2ω₀)`, with constants uniform in every parameter quantified
after `f`.

A conventional fixed-level prime Bombieri–Vinogradov input has the signature already proved in FormalPantheon:

```lean
BoundedGaps.Maynard.unconditional_bombieriVinogradov :
  ∀ theta : ℝ, 0 < theta → theta < 1 / 2 →
    BoundedGaps.Maynard.hasPrimeLevel theta
```

Polymath Theorem 2.9 supplies a bilinear estimate to
`x^(1/2) log(x)^(-B)`, but its discrepancy is over the entire finite support
of `α*β`. It has no `[x,2x]` output cutoff. Milestone 3E gives an explicit
counterexample showing that its hypotheses do not imply the sharply
truncated version, even when both factors have the Siegel–Walfisz property.
In particular, output truncation is not factor truncation, and
Siegel–Walfisz is not inherited by arbitrary interval pieces.

Milestone 3F strengthens the negative conclusion. The following version with
only global SW is **false**; it is retained here solely as the rejected
interface that must not be implemented:

```lean
def FalseSharpIntervalBilinearBV (classData : CoeffClassData)
    (epsilon : ℝ) : Prop :=
  0 < epsilon →
  ∀ power : ℝ, 0 < power →
    ∃ B C : ℝ, ∃ X0 : ℕ,
      0 < B ∧ 0 ≤ C ∧ 3 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
      ∀ M N : ℝ,
      ∀ alpha beta : ℕ → ℂ,
        CoeffAt classData x M alpha →
        CoeffAt classData x N beta →
        ScalesMultiplyToX classData x M N →
        Real.rpow (x : ℝ) epsilon ≤ N →
        GlobalSiegelWalfisz classData beta →
        sharpBilinearDiscrepancySum x B alpha beta ≤
          C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) power
```

The modulo-3 balanced-block example in `SHARP_OUTPUT_BV_RESOLUTION.md`
satisfies every displayed premise, belongs to Definition 9's printed class,
and makes even a genuine-cell modulus sum `Omega(x)`. Thus Proposition 3 is
false for its universal printed Type-II class.

The valid repaired interface replaces `GlobalSiegelWalfisz` by a property
uniform under arbitrary interval restrictions (or the equivalent
polylog-height Mellin-twist property):

```lean
def IntervalSWSharpBilinearBV (classData : CoeffClassData)
    (epsilon : ℝ) : Prop :=
  0 < epsilon →
  ∀ power : ℝ, 0 < power →
    ∃ B C : ℝ, ∃ X0 : ℕ,
      0 < B ∧ 0 ≤ C ∧ 3 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
      ∀ M N : ℝ,
      ∀ alpha beta : ℕ → ℂ,
        CoeffAt classData x M alpha →
        CoeffAt classData x N beta →
        ScalesMultiplyToX classData x M N →
        Real.rpow (x : ℝ) epsilon ≤ N →
        IntervalSiegelWalfisz classData x N beta →
        sharpBilinearDiscrepancySum x B alpha beta ≤
          C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) power
```

Here `sharpBilinearDiscrepancySum` is the sum over
`q≤x^(1/2)log(x)^(-B)`, supremized over primitive residues, of the
discrepancy of `(alpha*beta)` restricted to the exact integer interval
`[x,2x]` (or `[⌈x⌉,⌊2x⌋]` in a real-scale formulation). This all-moduli
form follows at the mathematical level from Polymath Theorem 2.9 by the
smooth cutoff/Mellin proof in Fouvry--Radziwill, arXiv:1811.08672,
pp. 25--26. It is stronger than the logically minimal cell-restricted input.
The remaining theorem is structural: every Type-II term actually generated
by Proposition 2 must be proved to have the required local property.

For an exact dyadic upper constant `K_q≥1`, define

```text
κ(B,K_q,x) = (B * log (log x) + log K_q) / (2 * log x).
```

After `IntervalSWSharpBilinearBV` chooses `B`, split the varying branch at
`ω₀=-κ(B,K_q,x)`. The far part lies under the logarithmic cutoff. On the
residual strip, the zero-face partition plus Lemmas 13 and 6 applies once
`58ε_d≤η` and the common threshold ensures

```text
2 * (B * log (log x) + log K_q) / log x ≤ 9ε_d
4 * (B * log (log x) + log K_q) / log x ≤ 55ε_d.
```

Thus the required order is: fix support/class data, `xi2`, `eta`, and
`K_q`; choose `ε_d` with `58ε_d≤η` and fixed strict Type-IIc slack; for
every requested error power choose `B,C,X0`; only then universally quantify
`x`, cells, scales, sequences, `γ`, residues, and `ω₀∈[-η,0)`. The endpoint
`ω₀=0` remains exclusively in the nonnegative Type-IIc branch.

A stronger prefix-maximal bilinear theorem under an equally local premise
would also suffice, since
`1_[x,2x]=1_{n≤⌊2x⌋}-1_{n≤⌈x⌉-1}` and discrepancy is linear. That maximal
theorem is not Polymath Theorem 2.9 either. Fouvry--Radziwill source the
generic local-SW adapter, but the Stadlmann sources do not prove that every
minorant term belongs to the narrower class. Therefore
`NegativeOmegaDistribution` remains a target and is not an authorized
assumption.

## Universal analytic-input structure

After the generated coefficient class and its membership theorem have been
proved, a structure could have the following shape. This is deliberately
not ready to implement. Every conclusion is universal; no field mentions
`engelsmaTuple48`, 236, the public bounded-gap proposition, or its liminf
equivalent.

```lean
structure AnalyticInput where
  modifiedSieve :
    ∀ {k slices : ℕ}
      (H : Finset ℕ) (index : H ≃ Fin k)
      (P : SupportSliceData k slices)
      (rho : MinorantFamily) (c1 c2 beta : ℝ)
      (F : (Fin k → ℝ) → ℝ) (i : Fin k),
      BoundedGaps.IsAdmissible H →
      IsPrimeMinorant rho c2 →
      RealEquidistributedForRelevantModuli P rho →
      HasRoughSupport rho beta →
      HasMinorantMass rho c1 →
      BetaExceedsOneCaps P beta →
      ModifiedTrialAdmissible P F →
      HasStrictModifiedSieveRatio P i F c1 c2 →
      BoundedGaps.InfinitelyOftenAtLeastPrimeShifts H 2

  harmanMinorant :
    ∀ {k slices : ℕ}
      (P : SupportSliceData k slices)
      (xi1 xi2 xi3 : ℝ),
      HarmanParameterConditions xi1 xi2 xi3 →
      (∀ f : ℕ → ℕ → ℂ,
        GeneratedMinorantClass P xi1 xi2 xi3 f →
        EquidistributedForRelevantModuli P f) →
      ∃ rho : MinorantFamily, ∃ c1 c2 beta : ℝ,
        HarmanMinorantSpec P xi1 xi2 xi3 rho c1 c2 beta

  correctedProp3Generated :
    ∀ {k slices : ℕ}
      (P : SupportSliceData k slices)
      (xi1 xi2 xi3 eta : ℝ),
      0 < eta →
      HarmanParameterConditions xi1 xi2 xi3 →
      Prop3Global P xi1 xi2 xi3 eta →
      Prop3FiniteLocalNonnegative P xi1 xi2 xi3 eta →
      NegativeOmegaDistribution P xi2 eta →
      ∀ f : ℕ → ℕ → ℂ,
        GeneratedMinorantClass P xi1 xi2 xi3 f →
        EquidistributedForRelevantModuli P f

  negativeOmega :
    ∀ {k slices : ℕ}
      (P : SupportSliceData k slices)
      (xi2 eta : ℝ),
      0 < eta →
      NegativeOmegaDistribution P xi2 eta
```

The three analytic layers are visible as separate fields. The negative
theorem is named rather than hidden in `correctedProp3Generated`. Before any
such structure is declared, an ordinary theorem (not a structure field)
must construct `GeneratedMinorantClass` membership for every term in the
minorant identity. Later unconditional work removes this structure by
constructing every field as a Lean term.

## Specialized conditional theorem

Once the finite support, trial-function, `c₁`, integral, and positive-enlargement theorems have no hypotheses, the public conditional spine has the exact signature

```lean
theorem conditional_H1_le_236
    (analytic : BoundedGaps.H1236.AnalyticInput) :
    BoundedGaps.H1236.boundedGapsStatement236
```

Its proof must perform only this chain:

1. construct the exact positive-enlargement support data at `k=48`;
2. use the finite global and local support theorems;
3. invoke `analytic.negativeOmega` and
   `analytic.correctedProp3Generated` to distribute every proved generated
   minorant convolution;
4. invoke `analytic.harmanMinorant` to obtain `rho,c₁,c₂,β` and their properties;
5. use the proved `c₁` bound and positive-`ε_s` integral crossing for the explicit trial function;
6. invoke `analytic.modifiedSieve`, universally instantiated with `engelsmaTuple48` and a proved equivalence to `Fin 48`;
7. apply existing `boundedGapsStatement236_of_engelsmaTuple48_two_prime_shifts`;
8. obtain the liminf form only afterward through existing `primeGapLiminfStatement236_iff_boundedGapsStatement236`.

No finite-certificate theorem and no 48-tuple conclusion is a field of `AnalyticInput`.

## Asymptotic and convention ledger

| Obligation | Tending parameter/filter | Fixed before the limit | Uniformly varying | Constants and thresholds | Source conversion |
|---|---|---|---|---|---|
| Minorant bounds | `x:ℕ → atTop` | `ξ_i`, support, `rho`, `c₂` | `n∈[x,2x]` | one `X₀` | manuscript real `x`; floor/ceiling adapter required |
| Rough support | `x:ℕ → atTop` | `β,rho` | `n,p` | one `X₀`; require `x≥3` for powers/logs | translate strict prime-factor exponent inequalities |
| Mass | `x:ℕ → atTop`, `Tendsto` | `ξ_i,c₁,rho` | Buchstab cells internally | all error terms share an eventual threshold | manuscript uses `(1-c₁+o(1))x/log x` |
| Relevant-modulus distribution | `x:ℕ → atTop` | support, function, `power,ε₀` | `a,q,j,j',m,m'` | `C,X₀` depend only on fixed data | dyadic `[x,2x]`; exact congruence/coprime conventions retained |
| Type I/II/III | `x:ℕ → atTop` | exponent triple plus a named positive slack | sequences and finite dyadic blocks satisfying their class | choose `ε_d` from slack, then `C,X₀`; no dependence on the varying triple inside the certified compact set | source uses `≍`, smooth cutoffs, and real scales; adapters required |
| Negative `ω₀` | `x:ℕ → atTop` | generated atom/support data, uniform interval-SW constants, `η`, exact dyadic constant, `ε_d` with `58ε_d≤η` | `ω₀↑0`, `γ`, cells, generated sequences, residues | `A` first; then smoothing/twist losses and `B,C,X₀`; common threshold also proves the `9ε_d/55ε_d` endpoint inequalities | Fouvry--Radziwill's Mellin argument adapts Polymath 2.9 under local SW; proving every minorant term has that structure is missing |
| Modified sieve | `x:ℕ → atTop` | tuple, support, minorant, trial function, constants | tuple coordinate, residue, divisor tuples | approximation parameter first, then shared large threshold | manuscript GPY interval is `[x,2x]`; existing finite positivity uses `[N,2N)`; endpoint difference needs an adapter |
| Positive enlargement | `ε_s → 0+`, `nhdsWithin 0 (Set.Ioi 0)` | limiting trial function and exact support parameters | integration variables | no `x`; an existential neighbourhood follows from a strict margin | direct rational `ε_*` would remove this limit |

All statements involving logarithms require eventual `x≥3`; all denominator-clearing steps require positive `I`, positive `x`, positive `log x`, and positive totients for `q≥1`.

## Existing theorem reuse

- Reuse unchanged: `BoundedGaps.InfinitelyOftenAtLeastPrimeShifts`, generic finite sieve sums and positivity, `exists_preSieveResidueClass`, `engelsmaTuple48_admissible`, `boundedGapsStatement236_of_engelsmaTuple48_two_prime_shifts`, and the liminf equivalence.
- Reuse as measure/finite-sum infrastructure: `maynardCubeOf`, `maynardInsertCoordinate`, square-divisor weights, and generic normalized-asymptotics positivity.
- Adapter required: ordinary PNT endpoint conventions. Fixed-`θ` prime
  Bombieri–Vinogradov is usable only where its exact strength suffices; it
  does not supply the negative Type-II branch. A sharp `[x,2x]` adapter from
  Polymath Theorem 2.9 is valid with interval-uniform SW, by the
  Fouvry--Radziwill Mellin argument. The same adapter from global SW is
  refuted. Every concrete generated minorant factor still needs the stronger
  property.
- Generalization required: all concrete ordinary-Maynard theorems specialized to `engelsmaTuple`, `Fin 105`, `smallKCandidate`, and the fixed statement at 600.
- Not interchangeable: existing `maynardI`, `maynardJ`, ordinary simplex support, concrete 105-dimensional asymptotics, and `boundedGapsStatement_of_bombieriVinogradov_and_pnt` do not implement the modified sieve.

## Statement-freeze failures

The architecture is precise enough to separate the work and to prevent a
conclusion-shaped analytic assumption. The `K` functional is now
statement-ready: Milestone 3C proved from the source-level derivation that it
is the full-dimensional same-coordinate penalty recorded above.

The `52ε_d` versus `100ε_d` discrepancy is resolved: 52 is forced by the
source proof and the unique `100ε_d` restatement is a typographical
inconsistency. The moving logarithmic split and endpoint-stability argument
are now fully quantified at the statement level.

The contract is **still not precise enough to implement `AnalyticInput.lean`
safely as a source-backed interface**. The original reason must be sharpened:
`SharpIntervalBilinearBV` over the printed arbitrary class is false, and so
is Proposition 3 with that Type-II quantifier. A generic sharp adapter is
source-backed after adding interval-uniform SW, but the audited sources do
not enumerate every term generated by Proposition 2 or prove that one
factor of each term satisfies this stronger property. Coding
`negativeOmega` or storing that membership as a structure field would turn
a refuted statement or an unproved decomposition into an assumption.

The independent `ξ₂≤ξ₃` versus `ξ₂<ξ₃` and zero-count discrepancies also
remain for review. See `SHARP_OUTPUT_BV_RESOLUTION.md` for the independent
counterexample audit, the repaired theorem, and the exact quantifier order.

## Independent replacement route status

The pinned cross-toolchain subproject at
`Verification/PrimeGaps186Bridge/` now proves the current public H₁ ≤ 236
statement conditional on the three explicit `PrimeGaps186` inputs. It does so
by transporting the stronger consecutive-prime liminf bound 186 and then using
the existing FormalPantheon liminf equivalence.

This does not authorize implementing the contract above and does not close any
of its analytic fields. In particular, it neither validates the false
universal Type-II clause nor supplies the missing generated-term/local-SW
theorem. The old Stadlmann route remains blocked exactly as recorded; the
PrimeGaps186 route is an independent replacement proof.

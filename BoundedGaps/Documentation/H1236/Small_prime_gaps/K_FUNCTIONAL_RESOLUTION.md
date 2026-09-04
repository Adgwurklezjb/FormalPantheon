# Resolution of the modified-sieve `K` functional

Status date: 2026-09-04.

## Result

**Classification: uniquely resolved from the source.**

Stadlmann's displayed definition has a transcription error: in the third
condition under the `K` integral, `t'_k` must be `t_k`. Thus `K` has one
distinguished-coordinate integration, not two. With the notation below, the
corrected formula is

\[
 K(F;\delta,A,B,\varepsilon)
 =\sum_{m=1}^{n}\sum_{m'=1}^{n}
 \int_{D^{\mathrm{same}}_{m,m'}(\varepsilon)}
   F(x,u)^2\,dx\,du,
\]

where

\[
\begin{aligned}
D^{\mathrm{same}}_{m,m'}(\varepsilon)=\{(x,u)\in[0,\infty)^{k-1}\times[0,\infty):{}&
 s(x)>\max(A_m-\varepsilon,A_{m'}-\varepsilon),\\
 &s(x)+u\in[A_{m-1}+\varepsilon,A_m+\varepsilon],\\
 &s(x)+u\in[A_{m'-1}+\varepsilon,A_{m'}+\varepsilon]\},
\end{aligned}
\]

and `s(x)=x_1+\cdots+x_{k-1}`. The support of `F` already confines the
effective domain to `[0,1]^k`. The manuscript uses closed intervals in
Definition 5 and half-open intervals in the support definition; the resulting
functionals agree because their differing boundary hyperplanes are null.

This conclusion is a reconstruction of the expression intended by the proof,
not a silent emendation of the PDF. The PDF remains defective as printed.

## Sources and evidence classes

The following sources were inspected.

- **Primary manuscript:** Julia Stadlmann, *Bounded Gaps Between Primes*,
  arXiv:2608.31126v1, Definition 5 on PDF p. 4; Lemma 1 on pp. 5--8;
  Lemma 2 on pp. 8--10; proof of Proposition 1 on pp. 10--11; and the matrix
  formula in Section 5.1 on p. 31.
- **Earlier primary source cited by the manuscript:** D. H. J. Polymath,
  [*Variants of the Selberg sieve, and bounded intervals containing many
  primes*](https://arxiv.org/abs/1407.4897), arXiv:1407.4897v4, Theorem 3.6
  and Section 5.3. The 2015 erratum only supplies missing bibliographic data
  and does not alter either passage.
- **Conditional dossier:** `Small_Gaps_236_Conditional_Proof.tex`, especially
  lines 125--154 and 732--777.
- **Verification packet:** the complete archive listing plus the selected
  members listed under “Saved implementation” below.
- **FormalPantheon:** a repository-wide search for Maynard's `I` and `J`, and
  `BoundedGaps/Maynard/Variational.lean` in full.

Statements explicitly printed in these sources are called **source
statements** below. Algebraic consequences are **deductions**. Program
behavior is **computational evidence** only.

## The printed formula and its defect

Definition 5, PDF p. 4, prints

\[
 \sum_{m,m'=1}^{n}
 \int\!\cdots\!\int
 F(t_1,\ldots,t_k)^2\,dt_1\cdots dt_k
\]

under the three conditions

\[
\begin{split}
t_1+\cdots+t_{k-1}&>\max(A_m-\varepsilon,A_{m'}-\varepsilon),\\
t_1+\cdots+t_{k-1}+t_k&\in[A_{m-1}+\varepsilon,A_m+\varepsilon],\\
t_1+\cdots+t_{k-1}+t'_k&\in[A_{m'-1}+\varepsilon,A_{m'}+\varepsilon].
\end{split}
\]

The sums bind `m,m'`; the displayed differentials bind `t_1,...,t_k`; and
`F` has exactly those `k` arguments. Nothing binds `t'_k`. The formula is
therefore not a function of `F,delta,A,B,epsilon` and is not a well-formed
integral. The same defect is repeated in the `K` contribution to `M_2` in
Section 5.1, PDF p. 31.

By contrast, `J` on p. 4 contains `t_k` and `t'_k` in both the integrand and
the differential `dt_k dt'_k`. Its scope is complete and its ambient
dimension is `k+1` (`k-1` common coordinates plus two fibre coordinates).

## Complete occurrence and variable-scope trace

| Location | Role of `K` | Variables actually integrated | Consequence |
|---|---|---|---|
| Definition 5, p. 4 | First definition | `t_1,...,t_k`; `t'_k` is free | Defective print |
| Proposition 1, equation (2.1), p. 5 | Penalty `-k c_2 K` | Refers back to Definition 5 | Does not repair scope |
| Lemma 1 statement, p. 5 | Defines discrete/product penalty `K_i` | One copy of every `t_s`, `s=1,...,k` | `K_i` is full-dimensional, not fibre-doubled |
| Lemma 1 proof, p. 6 | Defines `K_i(F,G;C)` | `t_1,...,t_k`, with `sum_(s != i) t_s>C` | Both factors are evaluated at the same point |
| Lemma 1, equations (2.3)--(2.6), pp. 6--8 | Passes from sliced `F` to product approximants | The `K_i` terms remain `k`-dimensional same-point products | Fixes the intended continuum penalty |
| Proposition 1 proof, equations (2.8)--(2.9), pp. 10--11 | Negative-minorant loss | The square of the bad component is evaluated by a non-prime sieve sum | Produces the same-point `K_i` |
| Section 5.1, p. 31 | `K` part of matrix `M_2` | `G_i(t)G_j(t) dt_1...dt_k` | Independently confirms one fibre coordinate; repeats only the bad domain symbol |
| Final application, p. 34 | Uses `c_2=0` | No `K` value is needed | The published 240 computation cannot disambiguate the typo |

There is no later manuscript calculation of a nonzero `K`.

## Reconstruction from Proposition 1

### 1. Finite sieve expression

For an admissible tuple `(h_1,...,h_k)`, Definition 4 uses

\[
 \nu(n)=\left(\sum_{j=1}^{n}\sum_{\ell=1}^{L_j}
 c_{j,\ell}\prod_{s=1}^{k}\lambda_{f_{j,\ell,s}}(n+h_s)
 \right)^2
\]

and

\[
 N(x;\rho,\nu)=
 \sum_{x\le n\le2x\atop n\equiv b\pmod W}
 \nu(n)\left(\sum_{i=1}^{k}\rho(n+h_i;x)-1\right).
\]

For a fixed coordinate `i`, Lemma 1 partitions the product components into
`L(j,i)` (their other-coordinate support stays below the safe threshold) and
`U(j,i)` (the complementary, exceptional components). Write the corresponding
finite divisor sums as

\[
 A_i(n)=\sum_{j}\sum_{\ell\in L(j,i)}c_{j,\ell}
          \prod_s\lambda_{f_{j,\ell,s}}(n+h_s),\qquad
 B_i(n)=\sum_{j}\sum_{\ell\in U(j,i)}c_{j,\ell}
          \prod_s\lambda_{f_{j,\ell,s}}(n+h_s).
\]

Then `nu(n)=(A_i(n)+B_i(n))^2`.

### 2. Where the negative part enters

The sole pointwise input is `rho(n+h_i;x)+c_2 >= 0`. Since `B_i(n)^2 >= 0`,

\[
\begin{aligned}
(A_i+B_i)^2\rho
 &= (A_i+B_i)^2(\rho+c_2)-c_2(A_i+B_i)^2\\
 &\ge (A_i^2+2A_iB_i)(\rho+c_2)-c_2(A_i+B_i)^2\\
 &= (A_i^2+2A_iB_i)\rho-c_2B_i^2.
\end{aligned}
\]

This is the displayed calculation on PDF p. 11. It answers three coefficient
questions at once.

- The penalty has one coordinate label `i`, because `L(j,i)` and `U(j,i)` are
  determined by the common sum with coordinate `i` omitted.
- The penalty is a square at the **same integer `n`**, so its continuum limit
  has one value of every integration coordinate.
- The coefficient is exactly `c_2`. The `+c_2` terms in the retained
  `A_i^2+2A_iB_i` part cancel the matching part of
  `-c_2(A_i+B_i)^2`, leaving only `-c_2B_i^2`. No factor `1+c_2`
  is produced.

### 3. Limiting integrals

Lemma 2 evaluates the terms carrying `rho` and gives `(1-c_1)J_i`. The
ordinary non-prime asymptotic, cited as Polymath Theorem 3.6, evaluates
`B_i(n)^2` and gives `K_i`. In Lemma 1's notation,

\[
 K_i=\sum_{j,j'}\sum_{\ell\in U(j,i)}\sum_{\ell'\in U(j',i)}
 c_{j,\ell}c_{j',\ell'}
 \prod_{s=1}^{k}\int_0^\infty
 f'_{j,\ell,s}(t_s)f'_{j',\ell',s}(t_s)\,dt_s.
\]

For smooth compactly supported product functions, Fubini turns the product of
one-dimensional integrals into

\[
 \int_{[0,\infty)^k}
 \left(\sum_{j,\ell\in U(j,i)}c_{j,\ell}
       \prod_s f'_{j,\ell,s}(t_s)\right)^2dt.
\]

It is consequently nonnegative. The expanded cross-term display need not be
termwise nonnegative; the reconstructed square is.

Before product approximation, p. 6 defines the underlying bilinear form

\[
 K_i(F,G;C)=\int_{\sum_{s\ne i}t_s>C}F(t)G(t)\,dt_1\cdots dt_k.
\]

Taking `F_j=F 1_{S_j}`, `G=F_{j'}`, and
`C=max(A_j-epsilon,A_{j'}-epsilon)` gives precisely the corrected
same-coordinate domain: the common sum is above the threshold and the
**same total point** is in both slice bands. Symmetry identifies every
coordinate contribution with the displayed last-coordinate functional, so
`sum_i K_i = k K`. This is the source of the combinatorial factor `k`.

### 4. Fubini, Tonelli, and Cauchy--Schwarz

- The manuscript does not name Fubini in Lemma 1, but its conversion between
  integrals of product functions and products of one-dimensional integrals
  uses Fubini; compact support and smoothness supply absolute integrability.
- Once the exceptional sum has been reconstructed as a square, Tonelli may be
  used for its nonnegative integral. Tonelli is not a mechanism for adding a
  second fibre coordinate.
- The Cauchy--Schwarz invocation on PDF p. 10 occurs in Lemma 2 after equation
  (2.7), to bound the aggregate equidistribution error `S_E`. It neither
  creates nor removes an integration coordinate and is not part of the `K`
  identification.

### 5. Comparison with the cited Polymath result

Polymath Theorem 3.6 is explicitly an asymptotic for **non-prime sums**. Its
main term is a product over `i=1,...,k` of one-dimensional integrals, which is
the product-function form of a `k`-dimensional same-point bilinear integral.
It has no second distinguished-coordinate integration. Polymath Section 5.3
also partitions safe and exceptional components, but its prime weight is
nonnegative, so the exceptional square can be discarded rather than paid for.
Stadlmann's `-c_2B_i^2` is exactly the additional loss caused by permitting a
negative minorant. Polymath therefore has no separate `K`, but the cited
non-prime main term agrees with `K_same`, not with a `k+1`-dimensional repair.

## Plausible well-typed corrections

Put

\[
 E_m^\varepsilon=[A_{m-1}+\varepsilon,A_m+\varepsilon],
 \qquad F_x(u)=F(x_1,\ldots,x_{k-1},u),
 \qquad s=s(x).
\]

All integrals below are over nonnegative coordinates. Indicators display the
entire domain explicitly.

### Candidate A: same-coordinate substitution (source-forced)

\[
 K_{\rm same}=\sum_{m,m'}\int_{x\in\mathbb R_+^{k-1}}
 \int_{u\in\mathbb R_+}
 1_{s>\max(A_m-\varepsilon,A_{m'}-\varepsilon)}
 1_{s+u\in E_m^\varepsilon}
 1_{s+u\in E_{m'}^\varepsilon}
 F_x(u)^2\,du\,dx.
\]

Ambient dimension: `k`. Bound variables: `m,m',x,u`; no free variables.
It is nonnegative term by term. It has the full-point `L^2` normalization of
`I`, while `J` has two fibre variables. It is exactly the bilinear form in
Lemma 1 with `F=G` and exactly the matrix contribution on p. 31 after the same
substitution.

Because the slice bands are disjoint apart from endpoints, this equals, up to
null boundaries, the useful diagonal normal form

\[
 K_{\rm diag}=\sum_m\int_x\int_u
 1_{s>A_m-\varepsilon}1_{s+u\in E_m^\varepsilon}
 F_x(u)^2\,du\,dx.
\]

`K_diag` is not a competing semantic choice; it is a proved simplification of
Candidate A once the band-partition and boundary lemmas are available.

### Candidate B: existential projection (saved-code convention)

\[
 K_{\exists}=\sum_{m,m'}\int_x\int_u
 1_{s>\max(A_m-\varepsilon,A_{m'}-\varepsilon)}
 1_{s+u\in E_m^\varepsilon}
 1_{\exists v\ge0,\ s+v\in E_{m'}^\varepsilon}
 F_x(u)^2\,du\,dx.
\]

Ambient dimension: `k`. Bound variables: `m,m',x,u`; `v` is bound by the
logical existential and is not integrated. It is nonnegative and `I`-like in
dimension. It is a possible way to bind the printed symbol, and it is the
explicit convention in the archived Python reference kernel. It is not the
form obtained from `B_i(n)^2`: it projects the second slice to the common
coordinates rather than requiring the second sliced factor at the same point.
It can differ from Candidate A when distinct enlarged bands are close enough
for that projection to meet the first band.

### Candidate C: add a missing differential, keep `F_x(u)^2`

\[
 K_{\rm volume}=\sum_{m,m'}\int_x\int_u\int_v
 1_{s>\max(A_m-\varepsilon,A_{m'}-\varepsilon)}
 1_{s+u\in E_m^\varepsilon}
 1_{s+v\in E_{m'}^\varepsilon}
 F_x(u)^2\,dv\,du\,dx.
\]

Ambient dimension: `k+1`. Bound variables: `m,m',x,u,v`; no free variables.
It is nonnegative, but it multiplies the first fibre's `L^2` mass by the
length of an unrelated second fibre. It has `J`-like scaling under coordinate
dilation and no counterpart in the finite square or Polymath Theorem 3.6.

### Candidate D: add a differential and a second factor

\[
 K_{\rm cross}=\sum_{m,m'}\int_x\int_u\int_v
 1_{s>\max(A_m-\varepsilon,A_{m'}-\varepsilon)}
 1_{s+u\in E_m^\varepsilon}
 1_{s+v\in E_{m'}^\varepsilon}
 F_x(u)F_x(v)\,dv\,du\,dx.
\]

Ambient dimension: `k+1`. Bound variables: `m,m',x,u,v`; no free variables.
Individual cross terms may have either sign, but the complete double sum is
nonnegative. Indeed, with

\[
 g_m(x)=1_{s>A_m-\varepsilon}
         \int_0^\infty 1_{s+u\in E_m^\varepsilon}F_x(u)\,du,
\]

the sum is `integral_x (sum_m g_m(x))^2`. This is a restricted fibre-square
and is structurally a `J` term, not the full-dimensional penalty generated by
`B_i(n)^2`.

Simply deleting the faulty third condition while retaining the `m'` sum would
leave an unexplained multiplicity and an `m'`-dependent threshold with no
second-slice witness. Deleting both that condition and the `m'` sum gives the
diagonal normal form of Candidate A. These are not additional credible
source interpretations.

## Comparison table

| Candidate | Dimension | Nonnegative? | Matches Proposition 1 derivation? | `K(F;0)=0` for dossier `F`? | Tends to zero as `epsilon -> 0+` for dossier `F`? | Saved implementation |
|---|---:|---|---|---|---|---|
| A `K_same` | `k` | Yes, termwise | **Yes** | Yes | Yes | Not the documented convention |
| B `K_exists` | `k` | Yes, termwise | No; replaces a same-point factor by a projection | Yes | Yes | **Implemented** by `exact_k_entry` |
| C `K_volume` | `k+1` | Yes, termwise | No; introduces a free-volume factor | Yes | Yes | Not implemented |
| D `K_cross` | `k+1` | Yes after the full double sum | No; gives a fibre-square | Yes | Yes | Not implemented |

For normalization, Candidate A and Candidate B scale with the `k`-dimensional
full-point measure, like `I`. Candidates C and D have an extra fibre measure,
like the expanded form of `J`. All are real scalars, so the quotient is
formally numerically typed for all four; “dimension-consistent” here refers to
the integration measure forced by the finite sieve main term, not physical
units.

Only Candidate A is consistent simultaneously with Definition 5's integrand
and differentials, the auxiliary `K_i` on p. 6, equations (2.3)--(2.6), the
finite square on p. 11, Polymath Theorem 3.6, and the matrix integrand on p. 31.

## Dossier and saved implementation

### What the dossier proves

The dossier imports Definition 5 rather than restating `K`. Lines 732--746
use only these facts: a nonzero point lies in a band ending at `A_j`, all
coordinates are nonnegative, and the penalty requires the common sum to be
strictly beyond a relevant upper endpoint. At `epsilon=0`, each of Candidates
A--D has an empty domain:

- an actual or integrated fibre condition gives `s+u<=A_m`, hence `s<=A_m`;
- the penalty gives `s>A_m` (and likewise for any witness band).

Thus the dossier's `K(F;0)=0` is symbolic, not numerical, and remains valid
for every candidate in the table. It does not distinguish them.

Lines 757--777 use no quantitative `K` value. For Candidate A,

\[
 s>A_m-\varepsilon,\quad s+u\le A_m+\varepsilon,\quad u\ge0
\]

imply `0<=u<2 epsilon` and confine `s` to a width at most `2 epsilon` near
`A_m`. A finite union of these strips has measure tending to zero. Absolute
continuity for the integrable function `F^2` therefore gives
`K_same(F;epsilon) -> 0`. The dossier's particular `F` is bounded and
compactly supported, which also supplies an elementary common majorant.

The same zero-limit follows for B--D: the witness condition confines `s` to a
`2 epsilon` strip, and in C--D the additional fibre also has length at most
`2 epsilon`. This limiting claim therefore does not distinguish the
candidates either. No quantitative upper bound is needed for the dossier's
existential positive-`epsilon` argument; such a bound would be needed to
certify a specified rational `epsilon_*`.

### What the packet computes

The archive was listed in full and selected members were extracted only to a
temporary directory. Relevant archive members and SHA-256 digests are:

| Archive member | SHA-256 | Evidence |
|---|---|---|
| `tmp/primegaps_exact/src/primegaps/integrals.py` | `9d5e527f7479ec450a94cd1a82ba21ab1e04cc0cf10ec98d46926a9abb4fb531` | Implements Candidate B |
| `tmp/primegaps_exact/docs/section5-engine.md` | `3c94356ee8cb3f76e286175d3636ab819fc3be7c53e6321779661f73de512b62` | Documents Candidate B as a convention and notes `c_2=0` for 240 |
| `tmp/primegaps_exact/tests/test_exact_integrals.py` | `b70a9a4b5777d114b24deee476f4c241ff6ca8af2f142df4f4f91b1a464e85df` | Numerically cross-checks small examples of that convention |
| `Small_Gaps_Improvement_Investigation.md` | `862f9d0d82c9f479be6c6b4a547a866d8d827f7de9b4aba1003b8c21fadca97e` | Uses only symbolic emptiness at the limiting support |

In `integrals.py`, `exact_k_entry` calls `_k_monomial`. For actual band `m`
and witness band `m'`, lines 452--458 impose

\[
 \max(A_m-\varepsilon,A_{m'}-\varepsilon)<s
 < A_{m'}+\varepsilon
\]

up to boundary conventions, together with the actual-coordinate condition
`s+u in E_m^epsilon`. The upper bound is exactly the projection of
`exists v>=0, s+v in E_m'^epsilon`. Both the actual coordinate and the idea of
`t'_k` occur, but only the actual `k` coordinates are integrated.

The kernel can therefore evaluate Candidate B directly in small or generic
polynomial examples. Its tests compare exact values to quadrature for the same
chosen convention; they do not establish that the convention is the
manuscript's theorem. The packet documentation itself says the choice is
immaterial for Stadlmann's published certificate because `c_2=0`.

No program in the packet's H1 <= 236 analysis calls `exact_k_entry` or
`exact_ijk_matrices` with the 236 trial data. Those programs compute support
checks, `I`, `J`, and the limiting ratio. Their only `K` claim is the symbolic
empty-region argument at `epsilon=0`; no saved program supplies a positive
`epsilon` value or a quantitative positive-`epsilon` `K` enclosure. Therefore
the 236 computation remains valid at the limiting support for all four
candidates, but the saved general-purpose Candidate B values must not be used
for the corrected contract.

## FormalPantheon comparison

A repository-wide search found the definitions of Maynard's functionals at
`BoundedGaps/Maynard/Variational.lean:66` and `:70`:

\[
 \operatorname{maynardI}(F)=\int_{[0,1]^k}F(t)^2\,dt,
\]

\[
 \operatorname{maynardJ}_i(F)=
 \int_{[0,1]^{k-1}}\left(\int_0^1F(x,u)\,du\right)^2dx.
\]

The file separately proves both nonnegative and records every integrability
condition in `MaynardAdmissible`. Other repository occurrences are uses,
bridges, or concrete evaluations of these two definitions; there is no
existing Maynard `K` definition. The corrected modified `K` is `I`-like in
being a restricted full-point square integral. Existing cube, coordinate
insertion, set-integral, and nonnegativity infrastructure is reusable, but the
ordinary simplex functionals are not definitions of Stadlmann's modified
ones.

## Proposed Lean interface

The proof is coordinatewise, so the safest interface exposes the distinguished
coordinate instead of choosing a last element of a possibly empty finite
type:

```lean
def supportCommonTotal
    (i : Fin k) (t : Fin k -> Real) : Real :=
  Finset.sum (Finset.univ.erase i) t

def modifiedKRegion
    (P : SupportSliceData k slices) (i : Fin k)
    (m m' : Fin slices) : Set (Fin k -> Real) :=
  {t | inUnitCube t ∧
    max (P.A m.succ - P.epsilon) (P.A m'.succ - P.epsilon) <
      supportCommonTotal i t ∧
    P.A m.castSucc + P.epsilon <= supportTotal t ∧
    supportTotal t <= P.A m.succ + P.epsilon ∧
    P.A m'.castSucc + P.epsilon <= supportTotal t ∧
    supportTotal t <= P.A m'.succ + P.epsilon}

noncomputable def modifiedKAt
    (P : SupportSliceData k slices) (i : Fin k)
    (F : (Fin k -> Real) -> Real) : Real :=
  Finset.sum Finset.univ fun m =>
    Finset.sum Finset.univ fun m' =>
      integral (fun t => F t ^ 2)
        (volume.restrict (modifiedKRegion P i m m'))
```

The snippet is an interface proposal, not a newly created Lean declaration.
Production code should also prove:

```lean
theorem modifiedKAt_nonneg ... : 0 <= modifiedKAt P i F

theorem modifiedKAt_eq_of_coordinateSymmetric
    (hF : CoordinateSymmetric F) (i i' : Fin k) :
    modifiedKAt P i F = modifiedKAt P i' F

theorem sum_modifiedKAt_eq
    (hF : CoordinateSymmetric F) (i : Fin k) :
    (Finset.sum Finset.univ fun j => modifiedKAt P j F) =
      k * modifiedKAt P i F
```

After requiring `0<k`, the scalar `modifiedK P F` may select any coordinate
and use the independence theorem. Using `modifiedKAt` directly in the
coordinatewise sieve theorem avoids hiding that choice.

## Remaining proof obligations

Resolution of the formula removes a statement-level blocker, but proves none
of the analytic sieve. The following work remains.

1. Formalize the band partition and show closed/half-open endpoint changes are
   null.
2. Prove measurability, integrability, nonnegativity, coordinate independence,
   and the diagonal simplification of `modifiedKAt`.
3. Formalize the `L/U` product approximation and show its full-dimensional
   penalty tends to Candidate A, including the order of the approximation
   parameters on pp. 5--8.
4. Prove the non-prime main-term theorem needed for `B_i(n)^2`; the cited
   Polymath theorem is not yet a FormalPantheon theorem of the required
   modified-support generality.
5. Prove the algebraic lower bound from `rho >= -c_2` and the exact cancellation
   leaving `c_2B_i^2`.
6. Prove the finite sum over coordinates gives the factor `k`.
7. For the dossier trial function, prove `K(F;0)=0` with the selected endpoint
   convention and prove `modifiedKAt(F;epsilon) -> 0` as `epsilon -> 0+`.
8. Do not reuse the archive's Candidate B evaluator for a positive-enlargement
   certificate. A future explicit `epsilon_*` route needs a new generator for
   Candidate A and a proved checker.

## Audit conclusion

The intended functional is uniquely determined by the proof as Candidate A.
Author clarification is not necessary to state `K`: the auxiliary definition
on p. 6, the product approximation on pp. 6--8, the finite-square argument on
p. 11, and the matrix integrand on p. 31 all force a `k`-dimensional
same-coordinate penalty. The archive's existential convention is contrary
computational evidence, but its authors explicitly insulated the published
240 result from that choice by using `c_2=0`.

The `K` statement blocker may therefore be removed from the analytic contract.
The highest-priority remaining statement blocker is the negative-`omega_0`
distribution branch: the proposed repair still lacks a theorem uniform as
`omega_0` approaches zero from below.

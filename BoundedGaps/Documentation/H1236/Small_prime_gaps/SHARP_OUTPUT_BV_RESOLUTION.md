# Resolution of the sharp-output bilinear Bombieri--Vinogradov blocker

Status date: 2026-09-04. This is a source and proof audit. It does not prove
`H₁ ≤ 236`, and it does not authorize an analytic assumption in Lean.

## Executive decision

The Milestone 3E counterexample survives every hypothesis check. In fact it
can be summed over squarefree moduli in genuine nonzero cells of Stadlmann's
`Q*`, where it gives an `Omega(x)` left-hand side. Consequently:

1. the proposed `SharpIntervalBilinearBV` for the manuscript's arbitrary
   Type-II class is **false**, not merely absent from the literature;
2. Proposition 3 is false with Definition 9's universal Type-II quantifier as
   printed;
3. Polymath Theorem 2.9 cannot be adapted by an output cutoff from its stated
   hypotheses alone;
4. a valid generic adapter *can* be derived after strengthening one factor to
   interval-uniform (equivalently, sufficiently uniform Mellin-twist)
   Siegel--Walfisz. Fouvry--Radziwill give this exact smoothing/Mellin
   mechanism in their proof of Corollary 1.1;
5. the explicit Polymath Heath--Brown atoms have the kind of local structure
   needed for that repair, but Stadlmann's 2025/2026 reductions do not list
   and verify every term produced by the Harman minorant. Narrowing
   Proposition 3 also requires Proposition 2 to be restated and reproved for
   that generated subclass.

The negative-`omega_0` branch therefore remains **not justified for the
conditional 236 chain**. `AnalyticInput.lean` is not authorized.

## Source ledger for this decision

| Source | Exact locations used | What it establishes |
|---|---|---|
| J. Stadlmann, *Bounded Gaps Between Primes*, arXiv:2608.31126v1 | Definition 6, PDF p. 12, TeX 532--545; Definition 7, pp. 12--13, TeX 554--573; Definition 9, p. 21, TeX 1104--1114; Proposition 2, pp. 21--24, TeX 1118--1242; Proposition 3 and Case II, pp. 27--30, TeX 1395--1447, 1536--1700 | The printed coefficient class is arbitrary, signed, divisor/polylog bounded, fixed-multiple supported, and globally SW. The conclusion uses the sharp output interval. No atom provenance or local-SW premise is present. |
| J. Stadlmann, *On primes in arithmetic progressions and bounded gaps between many primes*, arXiv:2309.00425v3 | Lemma 18, PDF pp. 34--35, TeX 1777--1800; Buchstab equations (4.2)--(4.5), p. 36, TeX 1831--1849; Lemmas 19--22, pp. 35--39, TeX 1803--1974 | The predecessor repeats the broad Type-II class, then appeals to direct Buchstab groupings, Baker--Weingartner, and Heath--Brown decompositions without a complete generated-term/local-SW ledger. |
| D. H. J. Polymath, *New equidistribution estimates of Zhang type*, arXiv:1402.0811v3 | discrepancy (1.1), PDF p. 6; Definition 2.5, p. 9; Theorem 2.9, p. 11; proof of Lemma 2.7, pp. 15--19, especially (3.9)--(3.13); Lemma 3.4(iii), p. 19; Remark 3.5, p. 20 | Theorem 2.9 is full-support. The application to primes removes a sharp cutoff collectively after an ultra-fine Heath--Brown partition and separately proves distribution for the actual atoms. |
| E. Fouvry and M. Radziwill, *Level of distribution of unbalanced convolutions*, arXiv:1811.08672, Ann. ENS 55 (2022), DOI 10.24033/asens.2501 | Definition 1, PDF pp. 2--3, equation (3); Corollary 1.1, p. 3, equation (4); Proposition 8.1, p. 24, equation (57); proof of Corollary 1.1, pp. 25--26, equations (58)--(62) | Their SW condition is uniform on every dyadic interval. They convert a full-support bilinear estimate to the sharp condition `x<mn≤2x` by smoothing, a divisor-bound collar estimate, Mellin inversion, truncation, and uniform SW for twists. |
| G. Harman, R. C. Baker and A. Weingartner antecedent used by Stadlmann | Baker--Weingartner Lemma 14, Acta Arith. 162 (2014), pp. 178--179, (4.1)--(4.3); Baker--Irving arXiv:1505.01815, Type 2 statement and pp. containing TeX 395--410 | Lemma 14 asks for estimates against arbitrary bounded test arrays on a sharp output weight. The cited Type-II result assumes SW factors. The source chain does not exhibit a common exceptional-modulus argument or reduce all arbitrary tests to a finite SW-generated list. |

The local Stadlmann PDF is the authoritative copy for its page references.
The arXiv TeX files were used to pin exact formulas and source lines. Attempts
to retrieve a valid primary scan of Bombieri--Friedlander--Iwaniec Theorem 0
from its publisher endpoints returned access/error HTML, not a PDF. This does
not affect the conclusion: Polymath's own (1.1) and Theorem 2.9 are explicit,
and Fouvry--Radziwill supply the needed sharp-conversion proof under their
stronger Definition 1.

## Independent audit of the modulo-3 counterexample

### Definition, support, and size

Let `T` tend to infinity through multiples of 60, put `x=T^2`, `M=N=T`,
and `h=1/10`. Let `chi_3` be the nonprincipal real character modulo 3. Put

```text
t(m) = -1  for T ≤ m < T+T/20,
        1  for T+T/20 ≤ m ≤ T+T/10,
        0  otherwise;

s(n) = -1  for T/2 ≤ n < T,
        1  for T ≤ n ≤ 3T/2,
        0  otherwise.
```

Define `alpha(m)=t(m)chi_3(m)` and `beta(n)=s(n)chi_3(n)`. Then both
sequences are real and 1-bounded. Their supports lie in `[T,1.1T]` and
`[0.5T,1.5T]`; `MN=x`; and `N=x^(1/2)`. Thus all support, growth, product,
and lower-scale hypotheses of Polymath Theorem 2.9 hold with fixed constants.

### Full Siegel--Walfisz quantifiers

For either signed block `sigma=t` or `s`, and every `q,r≥1` and primitive
`a mod q`, expand `1_(n,r)=1` as `sum_(d|r) mu(d) 1_(d|n)`.

- If `(d,q)>1`, the congruence and divisibility conditions are inconsistent.
- If `(d,q)=1` and `3` does not divide `qd`, CRT gives one progression modulo
  `qd`; `chi_3` has a bounded sum on each sign block.
- If `3|d`, every summand is zero.
- If `3|q`, `chi_3` is constant on the progression, but the adjacent
  opposite-sign blocks have equal length, so their progression counts differ
  by `O(1)`.

The residue-class term is therefore `O(tau(r))`. Expanding
`1_(n,qr)=1` similarly makes the normalized coprime main numerator
`O(tau(qr))`. Hence, with one absolute `C`,

```text
|Delta((sigma*chi_3) 1_(.,r)=1; a(q))| ≤ C tau(qr).
```

For every fixed saving `S`, `1 ≪_S T/log(x)^S`; enlarging the constant to
cover bounded `x` proves the exact global SW order

```text
forall S, exists C_S, forall x>1, q,r≥1, (a,q)=1.
```

The constants are independent of the later `T,q,r,a`. This proves SW for
both factors, although Theorem 2.9 requires it only for `beta`.

### Complete support versus sharp output

For modulus 3 and residue 1,

```text
Delta(alpha*beta;1(3))
  = (1/2) (sum_(3∤m) t(m)) (sum_(3∤n) s(n)) = 0.
```

The equality is exact for `60|T`: each opposing pair of blocks contains the
same number of integers coprime to 3. Thus the example is compatible with
the full-support conclusion of Theorem 2.9.

For the sharp product region `T^2≤mn≤2T^2`, progression counting gives

```text
Delta((alpha*beta)1_[x,2x];1(3))
  = -(2/9)c_h x + O(T),
c_h = log((1+h/2)^2/(1+h)) > 0.
```

Indeed, writing `m=T(1+u)`, the whole upper `s` block is selected and
cancels between the two `t` blocks, while the selected part of the lower
block has length `Tu/(1+u)`. The difference of its integrals over
`[0,h/2]` and `[h/2,h]` is `c_h>0`. Endpoint and floor effects are `O(T)`.
For `h=1/10`, the limiting ratio is `-0.000504477452...`.

The exact verifier `verify_sharp_counterexample.py` computes the finite
sums as rational numbers. Its output is:

```text
predicted limiting sharp discrepancy/x = -0.000504477452
T=  60 full=    0 sharp=      -2 sharp/x=-0.000555555556
T= 120 full=    0 sharp=      -8 sharp/x=-0.000555555556
T= 240 full=    0 sharp=   -61/2 sharp/x=-0.000529513889
T= 480 full=    0 sharp=  -237/2 sharp/x=-0.000514322917
T= 960 full=    0 sharp=    -468 sharp/x=-0.000507812500
```

This computation corroborates but does not replace the preceding proof.

### Compatibility with the manuscript class and genuine cells

Definition 9's Type-II clause says only `f=alpha*beta`, `MN≈x`, both
factors globally SW, and
`xi_2-eta≤log_x N≤1-xi_2+eta`. With `log_x N=1/2`, the example belongs to
that printed class. There is no positivity hypothesis, and the actual
Heath--Brown construction is signed in any event.

The fixed modulus 3 is enough to refute the proposed all-moduli theorem.
One can also avoid the manuscript's independent ambiguity at zero-count
cells. Choose

```text
delta < theta1 < theta2 <
  min((1-epsilon0)B_(1,1),
      (1-epsilon0)(A_1-epsilon_s), 1/4)
```

and distinct primes `p,r in [x^theta1,x^theta2]`. For the dossier values,
`theta1=.02`, `theta2=.03` work. With `q=3pr`, take the genuine
`j=j'=1`, `m=m'=1` cell, `e=3`, `e'=1`, `f_1=p`, `f'_1=r`. For large
`x`, all caps hold, `ee'=3` is `x^delta`-smooth, and `q` is squarefree.
Uniform progression counting yields

```text
Delta_q = -c_h x phi(q)/q^2 + O(sqrt(x) tau(q)).
```

Summing over `p<r` in the two fixed exponent bands and using Mertens' theorem
for primes gives `Omega(x)`; the total error is
`O(x^(1/2+2theta2)/log(x)^2)=o(x)`. Thus Proposition 3 itself fails for
its declared universal class, including genuine nonzero cells. This does
not show that a concrete Heath--Brown atom fails; it shows that provenance
omitted from Definition 9 is mathematically essential.

## Reconstruction of the coefficients actually used

### What Proposition 3 prints

The printed Type-II class has these fields only:

- arbitrary real, possibly signed coefficient families depending on `x`;
- divisor/polylogarithmic size bounds with unspecified fixed exponents;
- support in `[cM,CM]` and `[c'N,C'N]` for fixed positive constants;
- `MN≈x` and `N=x^gamma` in the stated Type-II band;
- global full-support SW for both factors.

The individual supports put the convolution in a fixed-multiple interval
around `x`; they do not force `mn in [x,2x]`. The latter is solely the
output indicator in Definition 7 and Proposition 3. Case II on pp. 28--30
introduces no additional structure.

### What can be recovered from the intended Harman proof

Stadlmann 2025 has three levels of structure that are not represented in
Definition 9:

1. The direct Buchstab terms include a prime variable against a sifted
   remainder and a two-prime block against a remainder. Coupled inequalities
   are localized before grouping, but complete formulas for all local cells
   are not printed.
2. The three-prime route applies a Heath--Brown identity and introduces at
   most 40 atoms. Every subset convolution is assumed located at its product
   scale; sufficiently large atoms are smooth; subset products above a power
   threshold are SW; complementary subsets in the Type-II exponent band are
   grouped as `alpha,beta`.
3. The four- and five-prime routes make further direct and subset groupings.
   Prime indicators are nonnegative, but Möbius atoms and alternating
   Heath--Brown coefficients make the resulting factors signed.

Polymath Section 3 makes its own atom list explicit:

```text
psi_N mu_≤,  psi_N,  psi'_N = psi_N log(.)/log N,
Theta = 1 + log(x)^(-A0),
support in [Theta^(-1)N, Theta N].
```

It removes the product cutoff *collectively*: retain only cells whose scale
products meet `[x,2x]` up to a `Theta^(O(1))` collar, replace their sharp
terms by full cell convolutions, then bound the residual collar. Lemma
3.4(iii) proves SW for these actual atoms/subconvolutions before grouping.
This is not an inheritance theorem for an arbitrary member of Definition 9.

### Lean-ready repaired coefficient class

The weakest clean generic premise is one interval-hereditary factor. Freeze
all hidden constants in data rather than in `O` notation:

```lean
structure BilinearClassData where
  lowerSupport upperSupport : ℝ
  lowerProduct upperProduct : ℝ
  divisorExponent logExponent swTauExponent : ℕ
  coeffConstant : ℝ
  -- For each requested saving, named uniform constants and a threshold.
  swConstant : ℕ → ℝ
  swThreshold : ℕ → ℕ
```

Schematic predicates (not implemented here) are:

```lean
def IntervalSiegelWalfisz
    (D : BilinearClassData) (x N : ℕ) (beta : ℕ → ℂ) : Prop :=
  ∀ S : ℕ, ∀ L U q r : ℕ, ∀ a : ℤ,
    D.swThreshold S ≤ x → L ≤ U → Nat.Coprime a.natAbs q →
    |Delta ((beta * 1_[L,U]) * 1_(.,r)=1) a q| ≤
      D.swConstant S * tau(q*r)^(D.swTauExponent) *
        N / log(x)^S

def LocallySWBilinearData ... : Prop :=
  CoeffAt D x M alpha ∧ CoeffAt D x N beta ∧
  ScalesMultiplyToX D x M N ∧ x^kappa ≤ N ∧
  IntervalSiegelWalfisz D x N beta
```

The real implementation must settle integer versus real scales, complex
absolute values, zero logarithms, and exact half-open interval conventions.
The predicate above displays the logical content: the constants are fixed
before `x`, the interval, moduli, residue, and sequence.

For the source-faithful specialization, define a *generated* class rather
than a proof-irrelevant label. Its data must expose:

- the finite atom list and a fixed maximum length;
- each atom kind (smooth, log-smooth, Möbius-smooth, prime shell, or a
  separately proved sifted factor), scale, support, coefficient bound, and
  local-SW theorem;
- the signed scalar and the complementary grouping partition;
- every localized Buchstab/coupled-inequality cell;
- a proof that the convolution equals the corresponding minorant term on
  `[x,2x]` plus an explicitly bounded endpoint collar.

Membership of every term must be a proved theorem. It must not be hidden as
a field of `AnalyticInput` merely to make the interface typecheck.

## Primary-source theorem ledger

### Polymath Theorem 2.9

For finitely supported coefficient sequences at scales `M,N`, with
`MN≈x`, `N≥x^epsilon`, and `beta` globally SW, for each `A` there is `B`
such that

```text
sum_(q≤x^(1/2)log(x)^(-B)) sup_((a,q)=1)
  |Delta(alpha*beta;a(q))| ≪ x log(x)^(-A).
```

Equation (1.1) sums the whole finite support. There is no interval or prefix
parameter. The theorem cites BFI Theorem 0 rather than proving a hidden
weighted variant.

### Fouvry--Radziwill's sharp conversion

Their Definition 1 assumes SW uniformly for every window `y<n≤2y`, every
`y≥2`, and every later `q,r,a`. Corollary 1.1 has the sharp condition
`x<mn≤2x`. The proof first establishes full-support Proposition 8.1 and
then does the following on pp. 25--26:

1. choose `Delta=log(X)^(-R)` and a smooth `f` equal to 1 on `[1,2]`,
   supported on `[1-Delta,2+Delta]`;
2. bound both endpoint collars by the divisor-function progression lemma;
   for symmetric divisor bounds `tau_k`, `R=2k+A-1` suffices;
3. use Mellin inversion
   `f(mn/x)=(2pi)^(-1) integral f~(it)(mn/x)^(-it)dt`;
4. use `|f~(it)|≪min(1,(Delta(1+|t|))^(-2))`;
5. truncate at
   `|t|≤log(X)^(A+2R+2k)=log(X)^(3A+6k-2)`;
6. by partial summation, retain SW uniformly for
   `beta_t(n)=beta(n)n^(-it)`; and
7. apply the full-support proposition with a larger internal saving and
   integrate.

For asymmetric bounds
`|alpha|≤tau_(k_alpha) log(x)^c_alpha` and
`|beta|≤tau_(k_beta) log(x)^c_beta`, let
`k_sum=k_alpha+k_beta`, `c_sum=c_alpha+c_beta`. A safe explicit bookkeeping
scheme is

```text
R ≥ A + k_sum + c_sum - 1,
H = A + 2R + k_sum + c_sum + 2,
A_internal ≥ A + R + H + 3.
```

The harmless `+2,+3` make all tail, integral-length, and finite dyadic-sum
losses strict; they are not claimed optimal. Invoke Theorem 2.9 for the
uniform twisted class at saving `A_internal`. Complex twists may be split
into four real terms if a real-valued formalization is retained.

This proves a mathematical adapter from Theorem 2.9 **provided** the local
SW constants are uniform at the enlarged saving and for all
`|t|≤log(x)^H`. It does not prove that Stadlmann's arbitrary global-SW class
has that property.

## Adapter routes A--F

### A. Support alignment

Ordinary dyadic rectangles leave a boundary of positive relative area and
fail. An ultra-fine multiplicative grid with
`Theta=1+log(x)^(-R)` has `log(x)^(O(R))` cells. Every interior cell lies
entirely inside or outside the output interval. Boundary cells lie in two
relative `O(log(x)^(-R))` collars. This route works with interval-SW pieces
and a divisor-progression collar bound, exactly as Polymath's Lemma 2.7
application does for its atoms. It fails for arbitrary global-SW factors.

### B. Hyperbola decomposition

Refining `{x≤mn≤2x}` into the same short multiplicative rectangles is valid.
The logarithmic number of rectangles is absorbed by requesting a larger
saving. Truncating `beta` to each rectangle must preserve SW uniformly;
that is precisely the extra interval-hereditary premise. Truncating the
convolution itself is not equivalent to this operation.

### C. Smooth cutoff and desmoothing

This works under the same stronger premise. The collar is not discarded by
geometry alone: its residue and normalized sums are majorized by a standard
divisor-function progression estimate. Choosing `R` as above makes the sum
over moduli `O(x/log(x)^A)`. Without the divisor estimate, desmoothing is
unjustified.

### D. Perron or Mellin inversion

Mellin inversion is the cleanest generic repair and is proved in the cited
Fouvry--Radziwill pages. The output weight separates into twists of both
factors; interval-SW plus partial summation supplies uniform SW for the
twisted factor up to the explicit polylogarithmic height. A raw Perron
formula does not weaken this premise and creates sharper endpoint errors.

### E. Prefix subtraction

The exact identity
`1_[ceil x,floor 2x]=1_(n≤floor 2x)-1_(n≤ceil x-1)` has no rounding error.
But Theorem 2.9 is neither prefix-uniform nor maximal. No audited source
supplies such a theorem from global SW, and the counterexample forbids it.

### F. Actual-coefficient specialization

Smooth, log-smooth, Möbius-smooth, and prime-shell atoms should satisfy
interval-SW from classical prefix estimates plus partial summation; the
property is stable under convolution with a controlled `L^1` factor. For at
most 40 atoms, a grouped Type-II factor of fixed positive total exponent
contains an atom of fixed positive exponent, so this strategy is plausible.

It is not complete in the audited sources. The direct sifted/coupled terms
are not fully enumerated, and Stadlmann 2025 Lemma 19's invocation of
Baker--Weingartner Lemma 14 has an additional uniform-test-sequence gap.
Therefore no claim that *every* minorant term belongs to the repaired class
is currently justified.

## Strongest supported theorem and weakest sufficient theorem

### Generic adapter proved at the mathematical level

`IntervalSWSharpBilinearBV(D,kappa)` has this order:

1. fix support-comparison constants, product-comparison constants,
   divisor/log bounds and constants, SW divisor exponent and its uniform
   constant/threshold functions, and `kappa>0`;
2. for every requested `A>0`, choose the smoothing exponent `R`, Mellin
   height exponent `H`, and internal saving `A_internal` as above;
3. apply full-support Polymath Theorem 2.9 uniformly to the resulting twist
   class, obtaining `B,C,X0`;
4. for every later `x≥X0`, `M,N`, `alpha,beta`, with `MN≈x`,
   `N≥x^kappa`, the frozen coefficient bounds and interval-SW for `beta`,
   obtain

```text
sum_(q≤x^(1/2)log(x)^(-B)) sup_((a,q)=1)
 |Delta((alpha*beta)1_[ceil x,floor 2x];a(q))|
 ≤ C x/log(x)^A.
```

`B,C,X0` may depend only on the data fixed in steps 1--3 and on `A`; they
may not depend on the later scales, interval endpoints, sequences, cells,
modulus, residue, `gamma`, or `omega_0`.

### Weakest input sufficient for the manuscript application

The logically weakest estimate restricts the preceding sum to the exact
squarefree moduli of one `Q*` cell and quantifies only over *proved generated
minorant Type-II terms*. A suitable target is:

```lean
theorem generatedHarmanTypeII_sharp_distribution
    (fixed support/cell/coefficient/atom data)
    (eps_d : ℝ) (h_eps : 0 < eps_d ∧ 58 * eps_d ≤ eta) :
  ∀ A > 0, ∃ B C X0,
  ∀ x ≥ X0,
  ∀ j j' m m' gamma omega0 alpha beta a,
    GeneratedMinorantTypeII ... alpha beta →
    -eta ≤ omega0 →
    omega0 ≤ -kappa B K_q x →
    xi2-eta ≤ gamma → gamma ≤ 1-xi2+eta →
    PrimitiveForRelevantModuli x a →
    cellSharpDiscrepancySum ... ≤ C*x/log(x)^A
```

The needed structural theorem before this estimate can be applied is:

```lean
theorem every_minorant_typeII_term_generated_locallySW :
  every Type-II term produced in the proof of Proposition 2, after the
  explicit ultra-fine localization and collar decomposition, belongs to
  GeneratedMinorantTypeII and has a factor satisfying the uniform
  interval-SW/twist-SW contract.
```

This membership/decomposition theorem is now the narrowest unresolved
source-level blocker. It must include the direct Buchstab, sifted,
Heath--Brown, and Baker--Weingartner routes, not just Polymath's prime atom.

## Full negative-branch quantifier order

The complete repaired branch must use this order.

1. Fix the support slices, `xi2`, `eta`, all coefficient/atom class data,
   `epsilon0`, and the exact dyadic upper constant `K_q≥1`.
2. Choose `eps_d>0` with `58 eps_d≤eta` and all fixed strict Type-IIc
   inequalities.
3. For each `A>0`, use the local-SW adapter to choose `B,C,X0`; enlarge
   `X0` once for every atom, cell, rounding, and Type-IIc threshold.
4. Only now quantify `x≥X0`, cells `j,j',m,m'`, generated sequences and
   scales, `gamma`, primitive residue `a`, and `omega_0 in [-eta,0)`.
5. Put
   `kappa(B,K_q,x)=(B log log x+log K_q)/(2 log x)`.
6. If `omega_0≤-kappa`, then
   `K_q x^(1/2+2omega_0)≤x^(1/2)log(x)^(-B)`. Apply the generated sharp
   theorem and restrict its nonnegative modulus sum to the exact squarefree
   cell subset. Floors and ceilings occur only in the displayed output
   interval.
7. If `-kappa<omega_0<0`, use the zero-face partition and Lemmas 13 and 6
   with loss 52. The shared threshold must also prove

```text
2(B log log x+log K_q)/log x ≤ 9 eps_d,
4(B log log x+log K_q)/log x ≤ 55 eps_d.
```

8. Keep `omega_0=0` exclusively in the existing nonnegative Type-IIc
   branch.

The far and near ranges cover the half-open negative interval and meet at
equality in the far range, with neither a gap nor a double use of zero.

## Compatibility with the `52 eps_d` correction

Nothing in the new counterexample or adapter alters Milestone 3E's source
calculation. Lemma 6 uses `52 eps_d`; Lemma 13 then has capacities

```text
gamma-2delta-8omega_0-58eps_d,
1/2-gamma-2omega_0-6eps_d,
delta+4omega_0+9eps_d,
8omega_0+55eps_d.
```

Thus `58eps_d≤eta` is still the exact endpoint-stability condition. It
controls only the near-zero Type-IIc branch; it does not cure the false
arbitrary-coefficient far branch.

## Lean decision

No Lean source was added. In particular, `AnalyticInput.lean` was not
created. It would be unsound project engineering to encode either the false
universal `SharpIntervalBilinearBV` or an unproved
`GeneratedMinorantTypeII` membership field as if it were established
analysis.

Safe next Lean work is limited to independent definitions and elementary
support/cutoff identities after the mathematical class is approved. The
analytic interface can proceed only after the generated-term theorem above
is proved and Proposition 2/3 are restated for that exact class.

## Remaining risks and human-review questions

1. Independently check the counterexample's uniform SW proof and the
   `q=3pr` embedding into genuine `m=m'=1` cells.
2. Approve the transfer of Fouvry--Radziwill's Mellin proof to Polymath
   Theorem 2.9, including uniform dependence of the theorem on the
   polylog-height twist class and the conservative loss exponents.
3. Obtain or reconstruct a complete generated-term ledger for every direct
   and Heath--Brown route in Proposition 2, with exact interval-SW proofs.
4. Resolve the Baker--Weingartner Lemma 14 arbitrary-test-array/common-
   exceptional-modulus issue in the Stadlmann 2025 Lemma 19 citation chain.
5. Have the author confirm whether Proposition 3 was intended only for
   generated Harman terms and supply the omitted restriction/proof; the
   precise query is in `AUTHOR_QUERY_SHARP_BV.md`.
6. Retain the independent reviews already registered for `52 eps_d`, the
   zero-count cells, `xi2=xi3`, and all floor/ceiling/dyadic constants.

The next highest-priority blocker is therefore not an unrestricted
sharp-output BV theorem. It is the complete, source-correct definition and
membership proof for the generated minorant Type-II terms, including their
uniform interval-SW property.

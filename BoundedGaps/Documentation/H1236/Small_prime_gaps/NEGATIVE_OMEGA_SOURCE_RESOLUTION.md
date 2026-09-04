# Source resolution for the negative-omega branch

Status date: 2026-09-04. This is a source-level audit, not a proof of
`H₁ ≤ 236`. The proposed result remains manuscript-conditional. No Lean source
file and no `AnalyticInput.lean` file was created in this milestone.

## Workspace snapshot

The milestone began with the requested read-only checks:

```text
$ pwd
/Users/z2265001/Documents/Lean/PrimeGap236/FormalPantheon/BoundedGaps

$ git status --short
?? Documentation/
```

Thus `Documentation/` was already untracked at entry; there were no tracked
changes to overwrite. The relevant permanent project files were:

```text
Documentation/H1236/Small_prime_gaps/ANALYTIC_CONTRACT.md
Documentation/H1236/Small_prime_gaps/GAP_REGISTER.md
Documentation/H1236/Small_prime_gaps/K_FUNCTIONAL_RESOLUTION.md
Documentation/H1236/Small_prime_gaps/Lean_Formalisation_Guideline_H1_236.tex
Documentation/H1236/Small_prime_gaps/SOURCE_LEDGER.md
Documentation/H1236/Small_prime_gaps/Small_Gaps_236_Conditional_Proof.tex
Documentation/H1236/Small_prime_gaps/Small_Gaps_236_Verification_Packet.tar.gz
Documentation/H1236/Small_prime_gaps/Stadlmann_2608.31126.pdf
```

## Primary-source ledger

| ID | Source inspected | Exact location used |
|---|---|---|
| S2608-PDF | Julia Stadlmann, *Bounded Gaps Between Primes*, arXiv:2608.31126v1 | permanent project PDF above; Lemma 6 pp. 13, 18--20; Lemma 13 pp. 25--26; Proposition 3 pp. 26--30 |
| S2608-TEX | source of arXiv:2608.31126v1 | arXiv source archive, `Bounded_Gaps_2.0.tex`, SHA-256 `c0d5d2317c77f4de7eacdef6e1d4b1eb6433e6240b5c09273b3d4eee99e6c3ba`; source lines 633--651, 960--1039, 1626--1700 |
| S2309-v1 | Julia Stadlmann, *On primes in arithmetic progressions and bounded gaps between many primes*, arXiv:2309.00425v1 | source `Primes_in_arithmetic_progressions.tex`, SHA-256 `5e72a44e3feabc970abbdb7f8d87448a677f23335fc15c88829a3d2dfe7457d7`; Definition of `D` and the proof corresponding to pp. 12--33 |
| S2309-v2 | same paper, arXiv:2309.00425v2 | source `Primes_in_arithmetic_progressions_2.tex`, SHA-256 `85bebaccf3ad2b269cef1fd4489dc193f72e47b6ee67509c3a8dbc7b8dc9ecd8`; source lines 500--532, 887--888, 1454--1522 |
| S2309-v3 | same paper, arXiv:2309.00425v3, published predecessor cited by S2608 | source `Primes_in_arithmetic_progressions.tex`, SHA-256 `60c0440f33d9cbf504470716491fb4d45b45b26d9a960c8e34ff2af500837a30`; Definition 3/table and Definition 7, source lines 290, 609--620, 649--653, 692--702 |
| P1402-v3 | D. H. J. Polymath, *New equidistribution estimates of Zhang type*, arXiv:1402.0811v3 | PDF pp. 6, 9--11 and Section 3 pp. 15--16; source `newgap.tex`, SHA-256 `fdffe1dfb7b820d8a45ecc0e07e2f7e17404e6e10b63db110c2d44afe42013ea`; equations (1.1), (2.4)--(2.5), Theorem 2.9, and the proof of Lemma 2.7 |

The arXiv abstracts and versioned source archives are primary publication
records: <https://arxiv.org/abs/2608.31126>,
<https://arxiv.org/abs/2309.00425>, and
<https://arxiv.org/abs/1402.0811>. Temporary copies used for extraction and
rendering are not project inputs and are not retained.

## Part A: the `52 epsilon'` / `100 epsilon'` discrepancy

### Every occurrence that determines the choice

Write `e` for Lemma 6's smoothing loss `epsilon'` and write `L` for the
coefficient in the third divisor range

\[
 r^2x^{2-\gamma-Le-\delta}d^{-4}<d_1
 <r^2x^{2-\gamma-Le}d^{-4}.
\]

The complete chain in S2608 is:

| Place | Printed loss | Role |
|---|---:|---|
| Lemma 6 statement, p. 13 | `L=52` | public definition of `D_IIc` |
| Lemma 6 proof opening, p. 18 | `L=100` | a single restatement of `D_IIc` |
| definition of the dyadic factor set `R`, p. 18 | `L=52` | the factor actually used in the proof |
| extraction of `d_1`, p. 19 | `52` | gives `Delta` of size `x^(2-gamma-52e)/(Q^4R^2)` |
| rewrite in terms of `H`, p. 19 | `50` | gives `Delta` of size `N/(q_0^2 x^(50e) H^2)` |
| shortened variable `Delta_1`, p. 19 | `55` | `Delta_1=Delta/x^(5e)` |
| lower bound for `m`, p. 19 | `55`, then `54` | substitutes `Delta_1`, then `RQ^2=x^(-e)q_0MH` |
| terminal estimates (3.5)--(3.9), pp. 19--20 | use `55`/`54` | produce the displayed aggregate losses `100e`, `200e`, and the final strict inequalities |
| Proposition 3, Type IIc reuse, p. 29 | `L=52` | repeats the Lemma 6 modulus family used with Lemma 13 |

There is no second use of `100` as the `d_1` loss. The other appearances of
`100e` on p. 20 are *derived aggregate losses* in terminal inequalities; they
are not definitions of `D_IIc` and do not support changing `L` to 100.

All three arXiv versions of the predecessor S2309 use

\[
 D=\frac{N}{x^{50e}H^2},\qquad
 \Delta_1=\frac{\Delta}{x^{5e}},\qquad
 \frac{N}{x^{\delta+55e}H^2}\ll\Delta_1
 \ll\frac{N}{x^{55e}H^2}.
\]

Versions 1 and 2 also explicitly use the resulting `54e` lower bound for
`m` and the same later `100e`, `200e`, and `400e` aggregate margins. Version
3 records the `50/55` data in Definition 3/Definition 7. The version history
therefore contains no competing `100e` definition for the extracted `d_1`.

### Complete loss calculation

S2608 p. 18 defines

\[
 H=\frac{x^eRQ^2}{q_0M},\qquad MN\asymp x,\qquad N=x^\gamma.
\]

Consequently

\[
 \frac{x^{2-\gamma-Le}}{Q^4R^2}
 \asymp
 \frac{N}{q_0^2x^{(L-2)e}H^2}.
\]

The cited predecessor quantity is `N/(x^(50e)H^2)`, with the new proof
inserting only `q_0^(-2)`. Hence `L-2=50`, so `L=52`. Shortening the
`Delta` interval by `x^(5e)` then gives loss `L+3=55`. Substitution in the
lower bound for `m`, followed by the displayed identity for `RQ^2`, gives
loss `L+2=54` (with harmless weakenings of positive powers of `q_0`). Thus:

| Stage | General `L` | `L=52` | `L=100` |
|---|---:|---:|---:|
| raw factor in `R` | `L` | 52 | 100 |
| `Delta` in `N/(q_0^2 x^(...) H^2)` | `L-2` | 50 | 98 |
| `Delta_1=Delta/x^(5e)` | `L+3` | 55 | 103 |
| lower-bound exponent after `RQ^2` substitution | `L+2` | 54 | 102 |

Only the middle column equals every downstream formula. Treating `100` as
a harmless stronger hypothesis is invalid: a smaller allowed `d_1` range
would change the proof to losses `98/103/102`, while the printed argument
immediately uses `50/55/54`. No containment argument in the manuscript
turns the `L=52` factor guaranteed by Lemma 13 into an `L=100` factor.

### Effect on the endpoint-stability repair

Substituting a general `L` into Lemma 13 (S2608 pp. 25--26) gives the four
near-zero capacities

\[
\begin{aligned}
C_1&=\gamma-2\delta-8\omega_0-(L+6)e,\\
C_2&=\tfrac12-\gamma-2\omega_0-6e,\\
C_3&=\delta+4\omega_0+9e,\\
C_4&=8\omega_0+(L+3)e.
\end{aligned}
\]

The zero-face Proposition 3 partition has bounds
`gamma-2delta-eta`, `1/2-gamma-eta`, `delta-eta`, and an empty fourth
bin. Reusing it for a sufficiently short negative strip requires

\[
 (L+6)e\leq\eta.
\]

If a dyadic block has exact upper bound
`q <= K_q x^(1/2+2 omega_0)` and Polymath's logarithmic cutoff is
`x^(1/2) log(x)^(-B)`, put

\[
 \kappa_{B,K_q}(x)=
 \frac{B\log\log x+\log K_q}{2\log x}.
\]

The far-negative branch is `omega_0 <= -kappa_(B,K_q)(x)`. On the residual
strip `-kappa_(B,K_q)(x)<omega_0<0`, the same zero-face partition satisfies
the four capacities once, in addition, `x` is large enough that

\[
 \frac{2(B\log\log x+\log K_q)}{\log x}\leq9e,
 \qquad
 \frac{4(B\log\log x+\log K_q)}{\log x}\leq(L+3)e.
\]

For the proof-forced value `L=52`, the precise margin is therefore

\[
 58e\leq\eta,qquad C_4=8\omega_0+55e,
\]

with the second large-`x` bound ending in `55e`. If one hypothetically
used `L=100`, endpoint stability alone could be arranged with
`106e<=eta` and a `103e` fourth-bin margin. That does not validate the
`L=100` Lemma 6 proof, whose `50/55/54` chain would still be wrong.

### Disposition

The evidence determines the intended value uniquely: **`52 epsilon'` is
forced by the proof, and the lone `100 epsilon'` at the opening of the
Lemma 6 proof is a typographical inconsistency.** This is a source deduction,
not an author-issued erratum, but it is strong enough to bind the formal
statement. No `AUTHOR_QUERY_LEMMA6.md` is needed. Independent expert review
of this deduction remains appropriate before publishing a correction.

## Part B: Polymath Theorem 2.9 and the sharp interval

### Exact source statement

Polymath defines, for any finitely supported `alpha : N -> C` and primitive
residue class `a (mod q)`, the signed discrepancy (p. 6, (1.1))

\[
 \Delta(\alpha;a(q))=
 \sum_{n\equiv a\pmod q}\alpha(n)
 -\frac1{\varphi(q)}\sum_{(n,q)=1}\alpha(n).
\]

Both sums run over the whole finite support. There is no implicit `n<=x`
or `[x,2x]` restriction.

Definition 2.5 (p. 9) says that a coefficient sequence is finitely
supported and satisfies
`|alpha(n)| << tau(n)^O(1) log(x)^O(1)`. It is located at scale `N` when
its support lies in `[cN,CN]` for fixed positive bounded constants `c<C`.
It has the Siegel--Walfisz property when, for every `q,r>=1`, every fixed
power `S`, and every primitive `a (mod q)`,

\[
 |\Delta(\alpha 1_{(\cdot,r)=1};a(q))|
 \ll \tau(qr)^{O(1)}N\log(x)^{-S}.
\]

Theorem 2.9 (p. 11) states: if `M,N >> 1`, `MN asymp x`,
`N >= x^epsilon` for a fixed `epsilon>0`, `alpha,beta` are coefficient
sequences at scales `M,N`, and `beta` has the Siegel--Walfisz property,
then for every fixed `A>0` there exists a fixed `B>0` such that

\[
 \sum_{q\le x^{1/2}\log(x)^{-B}}
 \sup_{a\in(\mathbb Z/q\mathbb Z)^\times}
 |\Delta(\alpha*\beta;a(q))|
 \ll x\log(x)^{-A}.
\]

The coefficient sequences may depend on `x`. A Lean statement must make
uniform the fixed support comparability constants, divisor/log-growth
exponents and constants, the fixed `epsilon`, and the constants in the
Siegel--Walfisz family. In that uniform class, the quantifier order is:

1. fix the coefficient-class data and `epsilon>0`;
2. for every requested `A>0`, choose `B>0`, an estimate constant `C`, and
   a threshold `X_0`;
3. for every `x>=X_0`, scales `M,N`, and admissible `alpha,beta` satisfying
   `MN asymp x` and `N>=x^epsilon`, the displayed sum is at most
   `C*x/log(x)^A`.

Neither `B`, `C`, nor `X_0` may depend on the subsequently chosen `x`,
scales, sequences, modulus, or residue. The theorem requires only `beta`
to be Siegel--Walfisz.

### Term-by-term comparison with Proposition 3

| Feature | Polymath Theorem 2.9 | Stadlmann Proposition 3 / Definition 3 |
|---|---|---|
| function inside `Delta` | full convolution `alpha*beta` | `(alpha*beta) 1_[x,2x]` |
| support | arbitrary fixed-multiple scale intervals; convolution support is their product interval | sharp integer points with real `x<=n<=2x` |
| residue | supremum over every primitive class modulo `q` | one fixed integer `a`, coprime to every prime `p<=x`, hence primitive for relevant `q` |
| normalization | `1/phi(q)` times full coprime-support sum | same normalization, but restricted to `[x,2x]` |
| moduli | every `q<=x^(1/2)log(x)^(-B)` | squarefree moduli in one relevant cell/dyadic block |
| coefficients | both coefficient sequences; only `beta` is SW | Type II has both factors SW, which is stronger but does not address truncation |
| error | `x log(x)^(-A)` | same required power saving, summed over relevant moduli |

The modulus and residue restrictions are harmless after proving inclusion
under the logarithmic cutoff. The output restriction is not harmless:
the product indicator `1_[x,2x](mn)` is not a function of `m` alone or of
`n` alone.

For exact natural endpoints,

\[
 1_{[x,2x]}(n)=1_{n\le\lfloor2x\rfloor}
                  -1_{n\le\lceil x\rceil-1}.
\]

There is no boundary error in this identity. What is missing is a theorem
uniform in the prefix endpoint; Theorem 2.9 has no such parameter.

### Refutation of a generic adapter

The hypotheses of Theorem 2.9 do not imply the same estimate after sharp
output truncation, even if **both** factors are Siegel--Walfisz. Here is a
self-contained counterexample.

Take integers `T` tending to infinity through multiples of 20, put
`M=N=T`, `x=T^2`, and `h=1/10`. Let `chi` be the nonprincipal real
Dirichlet character modulo 3. Define signs

\[
t(m)=\begin{cases}-1&M\le m<M(1+h/2),\\
                   +1&M(1+h/2)\le m\le M(1+h),\\0&\text{otherwise},
     \end{cases}
\]

and

\[
s(n)=\begin{cases}-1&N/2\le n<N,\\
                   +1&N\le n\le3N/2,\\0&\text{otherwise}.
     \end{cases}
\]

Set `alpha(m)=t(m)chi(m)` and `beta(n)=s(n)chi(n)`. These are bounded
coefficient sequences at scales `M,N`.

They are also uniformly Siegel--Walfisz. To see this, expand
`1_(n,r)=1` by Moebius inversion. On each resulting progression, either
`chi` oscillates with period three, giving a bounded sum on each sign
block, or `chi` is constant and the adjacent equal-length opposite-sign
blocks cancel up to an endpoint error. Both the progression term and the
coprime main term are therefore `O(tau(qr))`, uniformly in `q,r` and the
primitive residue. This is stronger than Definition 2.5(2.5), for every
fixed logarithmic power once `T` is large. The same proof applies to both
factors.

Now examine modulus `q=3`, residue `1`. Since
`chi(m)chi(n)=chi(mn)`, direct expansion of the convolution gives

\[
 \Delta((\alpha*\beta)1_{[x,2x]};1(3))
 =\frac12\sum_{\substack{x\le mn\le2x\\3\nmid mn}}t(m)s(n).
\]

For every `m=M(1+u)` with `0<=u<=h`, the whole upper beta block
`[N,3N/2]` lies in `[x/m,2x/m]`; its contribution cancels between the
two equal alpha blocks up to `O(M+N)`. In the lower beta block, the
selected interval is exactly `[N/(1+u),N)`, of length
`Nu/(1+u)`. Counting lattice points avoiding multiples of 3 gives

\[
 |\Delta((\alpha*\beta)1_{[x,2x]};1(3))|
 =\frac{2}{9}c_h x+O(M+N),
\]

where

\[
c_h=\int_{h/2}^{h}\frac{u}{1+u}\,du
       -\int_0^{h/2}\frac{u}{1+u}\,du>0
\]

because `u/(1+u)` is strictly increasing. Thus this single modulus has
sharp discrepancy `Omega(x)`, contradicting any `x/log(x)^A` bound.
Floors and closed endpoints alter only `O(M+N)=o(x)` pairs.

This rules out a theorem-level `[x,2x]` adapter from the exact Polymath
hypotheses. It also explains the failure of the usual proposed shortcuts:

- applying Theorem 2.9 directly estimates the full support, not the product
  cut;
- truncating the convolution is not truncating either factor;
- truncating a factor need not preserve Siegel--Walfisz (one sign block in
  the example has discrepancy of order its length modulo 3);
- subtracting two prefixes requires a prefix-uniform theorem not present in
  Theorem 2.9;
- a dyadic or finer partition needs Siegel--Walfisz for the new pieces.

Polymath's proof of Lemma 2.7 (Section 3, pp. 15--16) does use a
finer-than-dyadic smooth partition with
`Theta=1+log(x)^(-A_0)` and controls the boundary collar. Its factors are
the special Heath--Brown pieces `psi_N mu_<=`, `psi_N`, and `psi'_N`, for
which the paper separately establishes the needed distribution. That
argument is not a hereditary truncation theorem for arbitrary coefficient
sequences and does not repair Proposition 3's generic Type-II invocation.

### The weakest missing theorem and the valid elementary adapter

The direct missing analytic input is the following sharp bilinear theorem.
It is not Theorem 2.9 and has not been located in the audited sources.

**SharpIntervalBilinearBV.** Fix uniform coefficient-class data and
`epsilon>0`. For every `A>0` there exist `B>0`, `C>0`, and `X_0` such that,
for every `x>=X_0`, every scales `M,N` with `M,N>>1`, `MN asymp x`, and
`N>=x^epsilon`, and every coefficient sequences `alpha,beta` at those
scales with `beta` uniformly Siegel--Walfisz,

\[
 \sum_{q\le x^{1/2}\log(x)^{-B}}
 \sup_{a\in(\mathbb Z/q\mathbb Z)^\times}
 |\Delta((\alpha*\beta)1_{[\lceil x\rceil,\lfloor2x\rfloor]};a(q))|
 \le C\frac{x}{\log(x)^A}.
\]

The order is `class data, epsilon; A; exists B,C,X_0; x,M,N,alpha,beta`.
This all-moduli form is stronger than strictly necessary; the logically
weakest branch-specific input restricts the modulus sum to the actual
squarefree relevant cell and quantifies the fixed residue as in L-S03.

Alternatively, a maximal initial-segment theorem with the same order and

\[
 \sum_{q\le x^{1/2}\log(x)^{-B}}
 \sup_a\sup_{0\le Y\le\lfloor2x\rfloor}
 |\Delta((\alpha*\beta)1_{n\le Y};a(q))|
 \le C\frac{x}{\log(x)^A}
\]

would suffice. Linearity of `Delta` and the exact floor/ceiling identity
then prove the sharp theorem with constant `2C`. This is a rigorous
elementary adapter, but its maximal analytic premise is additional and is
also absent from Theorem 2.9.

## Lean-ready negative-branch quantifier order

The corrected branch must not quantify `omega_0` before choosing constants
which are meant to be uniform in it. A source-faithful order is:

1. fix support data `P`, `xi2`, `eta>0`, uniform coefficient-class data,
   and an exact dyadic upper constant `K_q>=1`;
2. choose `e>0` with `58e<=eta` and with the fixed strict Lemma 6
   inequalities retaining positive slack;
3. for every requested saving `A>0`, obtain `B,C_BV,X_BV` from
   `SharpIntervalBilinearBV`;
4. enlarge the common threshold so that the two displayed
   `kappa_(B,K_q)` inequalities hold and all Type-IIc estimates are valid;
5. for every later `x`, cell `j,j',m,m'`, Type-II scales and sequences,
   `gamma`, primitive residue, and `omega_0` with
   `-eta<=omega_0<0`:
   - if `omega_0<=-kappa_(B,K_q)(x)`, include the cell's squarefree dyadic
     moduli in the sharp BV range and take the relevant subset;
   - if `-kappa_(B,K_q)(x)<omega_0<0`, reuse the certified `omega_0=0`
     partition, apply Lemma 13 with the proof-forced loss 52, and invoke
     Lemma 6;
6. sum the finitely many cells with a common constant and threshold.

The endpoint `omega_0=0` remains solely in Proposition 3's nonnegative
Type-IIc branch. There is no gap or overlap.

In Lean-oriented schematic form, the missing reusable premise is:

```lean
def SharpIntervalBilinearBV (classData : CoeffClassData)
    (epsilon : Real) : Prop :=
  0 < epsilon ->
  forall A : Real, 0 < A ->
    exists B C : Real, exists X0 : Nat,
      0 < B /\ 0 <= C /\ 3 <= X0 /\
      forall x : Nat, X0 <= x ->
      forall M N : Real,
      forall alpha beta : Nat -> Complex,
        CoeffAt classData x M alpha ->
        CoeffAt classData x N beta ->
        ScalesMultiplyToX classData x M N ->
        (x : Real) ^ epsilon <= N ->
        UniformSiegelWalfisz classData beta ->
        sharpBilinearDiscrepancySum x B alpha beta <=
          C * (x : Real) / Real.log (x : Real) ^ A
```

The ASCII schematic deliberately records logical order rather than claiming
that these as-yet-unimplemented names already typecheck.

## Decision

- The `52/100` source blocker is closed in favor of `52`.
- The proposed direct `[x,2x]` adapter from Polymath Theorem 2.9 is
  refuted under the theorem's exact hypotheses.
- The negative branch is now precisely specified, but it depends on a new
  sharp-output (or stronger maximal-prefix) bilinear Bombieri--Vinogradov
  theorem not supplied by the sources.
- Therefore implementation of `AnalyticInput.lean` remains **NO-GO**. It
  would currently freeze an unproved analytic premise as if it had source
  authority.

Human mathematical review is still required to (1) validate the `52`
source correction for publication, (2) check the counterexample and agree
that the cited Polymath theorem has no hidden interval convention, (3)
supply or cite a proof of the sharp bilinear theorem with the stated
uniform constants, and (4) review the near-zero split, exact dyadic constant,
floor/ceiling normalization, and finite-cell summation before Lean coding.

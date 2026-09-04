# Gap register for the conditional H₁ ≤ 236 project

Status date: 2026-09-04. The current conclusion is manuscript-conditional. “Conditional spine” means a correctly stated theorem taking a universal analytic-input bundle as an argument; “unconditional theorem” means construction of that bundle by Lean proofs.

## Open issues

| ID | Severity | Exact location | Missing or ambiguous item | Required prerequisites | Proposed Lean module | Verification criterion | Blocks |
|---|---|---|---|---|---|---|---|
| H236-MATH-001 | Critical | Stadlmann Proposition 3(D), PDF pp. 27, 29--30; dossier lines 99--123 and G2 | Printed fourth capacity is impossible for `ω₀<0`. The moving split is exact and the near branch is repaired, but the far branch is false for the printed arbitrary class | Generated minorant Type-II class; interval-SW membership theorem; `IntervalSWSharpBilinearBV`; Lemmas 13/6 with loss 52; `58ε_d≤η` | `Analytic.NegativeOmega` | A fully quantified theorem covers only proved generated terms on `-η≤ω₀<0`, with constants uniform after the local-SW data are fixed | Conditional spine and unconditional theorem |
| H236-MATH-002 | Critical | Polymath Theorem 2.9 p. 11 and (1.1) p. 6; Fouvry--Radziwill Definition 1 pp. 2--3 and proof pp. 25--26; Stadlmann Definition 9 p. 21 and Proposition 3 p. 27 | `SharpIntervalBilinearBV` under global SW is refuted. The counterexample belongs to Definition 9 and gives `Ω(x)` even over genuine nonzero squarefree `Q*` cells, so Proposition 3 is false as printed. A generic sharp adapter is valid under interval-uniform SW | Approve and formalize the Fouvry--Radziwill smoothing/Mellin adapter; expose all uniform class/twist constants and exact endpoints | `Analytic.NegativeOmega` | `IntervalSWSharpBilinearBV` has order `class data,ε; A; ∃ losses,B,C,X₀; ∀x,M,N,α,β` and is proved from full-support BV plus local SW | Conditional spine and unconditional theorem |
| H236-SRC-030 | Critical | Stadlmann 2025 Lemmas 18--22, PDF pp. 34--39; 2026 Proposition 2 pp. 21--24 | The sources do not enumerate every direct, sifted, coupled, and Heath--Brown Type-II term or prove interval-SW for one factor of each. Narrowing Proposition 3 therefore requires a new Proposition 2 membership proof | Complete generated-term ledger, exact atom kinds/scales/groupings, local-SW closure, collar identity | `Analytic.HarmanGeneratedClass` | A theorem constructs membership for every minorant term without storing the result as an analytic assumption | Conditional spine and unconditional theorem |
| H236-SRC-031 | Critical | Baker--Weingartner Lemma 14, pp. 178--179, (4.1)--(4.3); Baker--Irving Type 2; Stadlmann 2025 Lemma 19 | Lemma 14 quantifies arbitrary bounded test arrays, while the cited Type-II theorem assumes SW factors; the proof chain does not display a common exceptional-modulus or generated-SW bridge | Reconstruct the complete alternative-sieve proof and prove the required uniform bridge, or replace the citation with a theorem whose hypotheses match | `Analytic.HarmanMinorant` | Every supremized test array/exceptional set has an explicit valid estimate with uniform constants | Conditional spine and unconditional theorem |
| H236-SRC-004 | Critical | Proposition 2 statement p. 21 and proof p. 22 | Statement permits `ξ₂≤ξ₃`; proof summary says it needs `ξ₂<ξ₃`; the dossier sets equality | Audit the cited 2025 Lemma 20/Type-III invocation, including every safety `η` | `Analytic.HarmanMinorant` | A proof works at exact equality, or revised parameters with all certificates rechecked are approved | Conditional spine and unconditional theorem |
| H236-SRC-005 | High | Proposition 3 quantifiers p. 27 and proof p. 27; Definition 2 pp. 3–4 | Proposition print uses `m,m'∈{1,…,⌊1/δ⌋}` but says the `m+m'=0` case is trivial; Definition 2 includes zero and the dossier’s 105 cases include it | Corrected range `0≤m,m'≤⌊1/δ⌋`; proof of zero/one-empty-block cases | `Analytic.Support`, `Certificates.Support` | Exact finite ranges are approved and every Q* cell is mapped to one certified case | Conditional spine and unconditional theorem |
| H236-SRC-006 | High | Definition 1 pp. 3–4 | Cap recurrence refers to `B_{j,m+1}` “for any m≥1” even at/outside the last matrix column | Explicit bounded quantifier or total plateau extension | `Analytic.Support` | Typechecked total cap function and lemma equivalent to the intended finite matrix statement | Conditional spine and unconditional theorem |
| H236-SRC-008 | High | Definition 2 p. 3 | The two total-factor bounds are asymmetric: `(A_j-ε_s)` for one factorization and `(A_{j'}+ε_s)` for the other | Audit against the GPY error-term derivation on pp. 8–10 | `Analytic.Support`, `Analytic.ModifiedSieve` | The asymmetry is confirmed or corrected and the modulus-containment proof is formalized | Conditional spine and unconditional theorem |
| H236-SRC-009 | Medium | Theorem 1, PDF p. 1 | The theorem sentence defines `H₁` but prints `H_m≤240` | Editorial correction | Publication source map | Corrected manuscript version says `H₁≤240` | Publication only |
| H236-SRC-010 | High | Proposition 1 p. 5 vs dossier lines 127–153 | Manuscript conclusion is `H₁≤H(k)`; dossier calls it a direct restatement yielding each admissible tuple’s diameter | Extract tuple-universal positivity from the proof, not merely from the proposition headline | `Analytic.ModifiedSieve` | Universal theorem returns `InfinitelyOftenAtLeastPrimeShifts H 2` for an arbitrary admissible `H` | Conditional spine and unconditional theorem |
| H236-SRC-011 | High | Definitions 3 and 7 pp. 4, 12 | Big-O quantifiers are prose; “sufficiently small” `ε_d` and dependence on exponent triples are not given as functions or thresholds | Fixed-slack compact parameter theorem; explicit constant/threshold order | `Analytic.DistributionDefinitions` | Every estimate is an eventual inequality with `C,X₀`, fixed/varying parameters, and dependencies visible | Conditional spine and unconditional theorem |
| H236-AN-012 | Critical | Proposition 1 proof pp. 5–11 | Modified Maynard/epsilon-enlargement theorem is absent from FormalPantheon | Smooth product approximation, modified S1/S2 main terms, equidistribution error, roughness, pre-sieving | `Analytic.ModifiedSieve` | Universal theorem in the contract compiles and has only foundational axioms | Unconditional theorem |
| H236-AN-013 | Critical | Proposition 2 pp. 21–24 | Harman minorant construction and Buchstab decomposition are absent | Coefficient classes, Buchstab identities, Type estimates, mass integrals, multiplicity bounds | `Analytic.HarmanMinorant` | Constructed `rho` has formula, `-24≤rho≤1_P`, roughness, mass, and exact distribution | Unconditional theorem |
| H236-AN-014 | High | Lemma 5 pp. 13, 17–18 | All three Type-I branches are missing | Polymath Theorem 5.8 variant, exponential-sum lemma, smooth cutoffs, dyadic adapters | `Analytic.TypeI` | Fixed-slack uniform finite-`x` theorem proves every branch and endpoint | Unconditional theorem |
| H236-AN-015 | Critical | Lemmas 3,4,6 pp. 12–20 | Type IIa, IIb, IIc distribution theorems are missing | Large-sieve/exponential-sum inputs, factorization, gcd sums, 2025 proof | `Analytic.TypeII` | Exact modulus predicates and error norm imply each proposition with explicit uniformity | Unconditional theorem |
| H236-AN-016 | Critical | Lemma 7 pp. 13, 20–21 | Type-III distribution theorem is missing and may require the deepest unavailable exponential-sum theory | Polymath Theorem 2.8(v), Lemma 7.5, smooth Type-III decomposition | `Analytic.TypeIII` | One complete vertical proof checks every external input and produces L-S03 | Unconditional theorem |
| H236-AN-017 | Critical | §3.3 p. 14 | Manuscript explicitly supplies only amendments to more than 50 pages of external proofs; Milestone 3E pinned the Polymath 2.9 source and all three predecessor versions only for the questions audited here, not every imported proof | Pin and recursively audit every remaining cited analytic source and proof segment | All `Analytic.Type*` modules | Every “copy the proof” step maps to a complete proved lemma | Unconditional theorem and publication |
| H236-AN-018 | High | Proposition 2 mass argument pp. 22–23 | Ordinary FormalPantheon PNT does not prove the five-prime short/dyadic asymptotics | Ordered-factor counting, boundary control, partial summation/Buchstab integration | `Analytic.HarmanMass` | `HasMinorantMass rho c1` is proved with the exact integral domains | Unconditional theorem |
| H236-FIN-019 | High | Dossier lines 683–730 | Rectangle bound on `c₁` needs direct confirmation that all five denominator factors are at least `β` on both exact regions | Approved regions, positivity, rational integration majorant | `Certificates.MinorantLoss` | Kernel-checked rational inequality equals the dossier fraction | Conditional spine if finite facts are not assumed; unconditional theorem |
| H236-FIN-020 | High | Dossier lines 283–501; packet replay logs | No Lean checker or complete Lean data for 105 support cases; saved LP logs contain digests rather than all dual vectors | Export full rational primal/dual data; sound weak-duality and packing checkers | `Certificates.RationalLP`, `Certificates.Support` | Lean proves `105=73+8+24` and all five local conditions without external trust | Conditional spine if finite facts are not assumed; unconditional theorem |
| H236-FIN-021 | Medium | Dossier lines 503–628 | Concrete Chebyshev profiles and exact `I` rational data are not in Lean | Generated fixed-length rational arrays; Chebyshev-to-power proof; exact integration checker | `TrialFunction`, `Certificates.Integrals` | Lean proves profile equality, regularity, positive exact `I`, and all six entries | Conditional spine if finite facts are not assumed; unconditional theorem |
| H236-FIN-022 | High | Dossier lines 630–680 | `J` bounds rely on rational geometry plus external Arb balls | Proof-producing rational interval/Bernstein certificates for all 2,655 cells | `Certificates.IntervalPolynomial`, `Certificates.Integrals` | Lean derives six enclosures and a rational lower bound strong enough for the crossing | Conditional spine if finite facts are not assumed; unconditional theorem |
| H236-FIN-023 | High | Dossier lines 732–777; `K_FUNCTIONAL_RESOLUTION.md` | For the resolved same-coordinate `K`, `K(F;0)=0` and convergence to positive enlargement remain unformalized, including boundary conventions | Prove the band partition, null boundaries, domination/absolute continuity, and shrinking-strip measure | `TrialFunction.PositiveEpsilon` | A no-hypothesis Lean theorem proves `K(F;0)=0`, produces a positive enlargement, and proves the strict ratio | Conditional spine if finite facts are not assumed; unconditional theorem |
| H236-FIN-024 | High | Guideline lines 699–716 | No explicit positive rational `ε_*` has been searched and certified | Extend exact geometry to positive enlargement and export rational certificate | `Certificates.PositiveEpsilonData` | A particular rational `ε_*>0` and exact `I,J,K` bounds are checked by Lean | Optional replacement for H236-FIN-023; would simplify both the conditional and unconditional paths |
| H236-LEAN-025 | High | Existing `Maynard/Variational.lean`, `EngelsmaCandidate.lean`, concrete chain | The production Maynard variational and asymptotic chain is specialized to ordinary simplex, `Fin 105`, `engelsmaTuple`, and `smallKCandidate` | Generalize only low-level finite/measure lemmas; write new modified functionals and main terms | `Analytic.ModifiedSieve`, `TrialFunction` | No new theorem imports the concrete diameter-600 candidate; generalized statements remain tuple/dimension universal | Unconditional theorem |
| H236-LEAN-026 | High | Existing BV statement; Polymath Theorem 2.9; Fouvry--Radziwill pp. 25--26 | Existing BV is fixed-level prime counting. Polymath 2.9 is full-support; its sharp conversion requires interval-SW. No generated coefficient definitions or membership proof exist in Lean | Formalize the local-SW adapter only after the generated class is approved; then prove subset/squarefree, dyadic, floor/ceiling, and endpoint adapters | `Analytic.NegativeOmega` | Exact implication for generated terms is proved, with no global-SW truncation axiom or hidden membership field | Conditional spine and unconditional theorem |
| H236-LEAN-027 | Medium | Manuscript real scales throughout; FormalPantheon natural endpoints | Real `x`, `N(x)`, `q≍Q`, and interval endpoints do not yet have a frozen Lean normalization | Natural floor/ceiling, dyadic block, and exponent/log adapters | `Foundations.AsymptoticScales` | A source-normalization theorem is proved in both directions wherever equivalence is claimed | Conditional spine and unconditional theorem |
| H236-LEAN-028 | Medium | Definition 6 p. 12 | Coefficient growth uses unquantified `O(1)` exponents and smooth derivative bounds | Select explicit exponent parameters and quantify them in the structures | `Analytic.DistributionDefinitions` | Two mathematical reviewers approve the unfolded class definitions | Conditional spine and unconditional theorem |
| H236-PUB-029 | High | Dossier abstract/status and manuscript v1 | Manuscript proves only 240, while 236 is a new dossier result conditional on the same unrefereed propositions plus new external computation | Independent analytic review and independent certificate replay | Paper/source map | Publication labels 236 “manuscript-conditional” until every critical item is closed | Publication |

## Resolved source issues

| ID | Resolution | Evidence | Residual work |
|---|---|---|---|
| H236-SRC-003 | **Resolved from the source:** in Definition 5's third `K` condition, replace the free `t'_k` by the already integrated `t_k`. `K` is a `k`-dimensional same-coordinate square integral. | Stadlmann Lemma 1 defines `K_i(F,G;C)=∫F(t)G(t)dt₁…dt_k` on p. 6; equations (2.3)–(2.6) retain this form; Proposition 1 p. 11 produces `-c₂B_i(n)^2`; Polymath Theorem 3.6 gives the full-dimensional non-prime main term; Section 5.1 p. 31 uses `G_a(t)G_b(t)dt₁…dt_k`. See `K_FUNCTIONAL_RESOLUTION.md`. | Implement the region and its measure theory; do not use the packet's conflicting existential-projection evaluator. Independent mathematical review remains prudent, but author clarification is not needed to bind the formula. |
| H236-SRC-007 | **Resolved from the proof in favor of `52ε_d`:** the lone `100ε_d` at the opening of the Lemma 6 proof is a typographical inconsistency. | Lemma 6 statement p. 13, the actual factor set p. 18, the `50/55/54` loss chain pp. 19–20, and Proposition 3 reuse p. 29 all force 52. Every arXiv version of the cited predecessor uses `D=N/(x^{50ε_d}H²)` and `Δ₁=Δ/x^{5ε_d}`. Algebra with `H=x^{ε_d}RQ²/(q₀M)` gives `L-2=50`, hence `L=52`. See `NEGATIVE_OMEGA_SOURCE_RESOLUTION.md`. | Use `52ε_d` in the eventual Type-IIc statement and require `58ε_d≤η` for endpoint stability. Independent review remains prudent for a publication correction, but no author query is needed to bind the formal statement. |

## Negative-ω₀ decision record

The fourth Type-IIc bin has capacity `8ω₀`. Every mass `y_i` is at least `δ>0`, and a partition bin has nonnegative load. If `ω₀<0`, even the empty fourth bin has load `0≤8ω₀` false. Thus the printed condition has no witnesses.

Milestone 3E determines the source-valid Lemma 6 loss to be 52. A general loss `L` gives Lemma 13 capacities
`γ-2δ-8ω₀-(L+6)ε_d`, `1/2-γ-2ω₀-6ε_d`,
`δ+4ω₀+9ε_d`, and `8ω₀+(L+3)ε_d`. Thus choose
`58ε_d≤η`. The zero-face partition is stable on a moving near-zero strip;
for dyadic upper constant `K_q`, its exact width is governed by
`κ=(B log log x+log K_q)/(2 log x)`, with eventual `9ε_d` and `55ε_d`
capacity inequalities.

This leaves a far branch under `x^(1/2)log(x)^(-B)`. Polymath Theorem 2.9
cannot discharge it for Definition 9's class: its discrepancy uses the full
convolution support, whereas Proposition 3 requires
`(α*β)1_[x,2x]`. Milestone 3F verifies that the counterexample belongs to
the printed class and strengthens it to an `Omega(x)` sum over genuine
nonzero squarefree `Q*` cells. Proposition 3 is therefore false as printed.

Fouvry--Radziwill's Definition 1 and pp. 25--26 prove a valid adapter when
one factor is SW uniformly on every dyadic interval. Their smoothing/Mellin
argument transfers to Polymath 2.9 after all class and twist constants are
made uniform. What remains missing is the proof that every Type-II term
actually generated in Proposition 2 has such a factor.

The only non-overlapping logical split is now precise:

- far negative: `-η≤ω₀≤-κ(B,K_q,x)`, requiring a proved generated term,
  `IntervalSWSharpBilinearBV`, and modulus-subset inclusion;
- near negative: `-κ(B,K_q,x)<ω₀<0`, using the zero-face partition and
  Lemmas 13 and 6 with loss 52;
- nonnegative Type-IIc: `0≤ω₀≤ω`, including the endpoint only here.

The endpoint repair and generic local-SW adapter are proved at the
mathematical statement level. The whole branch is not source-justified until
the generated coefficient class, membership/local-SW theorem, and narrowed
Propositions 2--3 are supplied.

## Positive-enlargement decision record

### Option A — dominated convergence and absolute continuity

Prove the dossier’s route at `ε_s→0+`: support nesting, unchanged `I`, almost-everywhere convergence of every `J` indicator, a common integrable majorant, shrinking `K` strips, and preservation of the strict margin. This requires no new numerical search and is the only route for which the dossier presently supplies a mathematical argument. Its disadvantages are a large measure-theory surface, dependence on the corrected `K`, and substantial risk around open/closed boundaries.

### Option B — explicit rational `ε_*`

Extend the rational geometry generator to a selected positive rational,
calculate `I,J,K` there using the resolved same-coordinate formula, export
proof-producing rational certificates, and check the denominator-cleared
inequality directly in Lean. The packet's existing existential-projection
`K` evaluator is not suitable for this task. This route avoids a
49-dimensional limiting argument and yields a clearer release theorem. Its
disadvantage is that no such certified value currently exists in the packet;
the current margin suggests plausibility but is not evidence of a particular
value.

### Decision

Prefer Option B **if and only if** a generator search produces a concrete rational value and complete certificates. This is the guideline’s recommended low-trust route. Until that happens, do not assert an `ε_*`; Option A remains the supported fallback and must be formalized in full. H236-FIN-024 is therefore exploratory, while H236-FIN-023 remains on the critical path.

## FormalPantheon module-reuse table

| Existing declaration/module | Reuse class | Required action for H₁ ≤ 236 |
|---|---|---|
| `BoundedGaps.H1236.boundedGapsStatementAt`, `boundedGapsStatement236` | Reuse unchanged | Public target already has the intended explicit prime-pair meaning. |
| `primeGapLiminfStatementAt_iff_boundedGapsStatementAt` and 236 specialization | Reuse unchanged | Keep after the explicit statement in the dependency chain. |
| `engelsmaTuple48_*` | Reuse unchanged | Exact cardinality, endpoints, upper bound, and admissibility are complete. |
| `boundedGapsStatementAt_of_two_prime_shifts`, 48-tuple specialization | Reuse unchanged | Final elementary bridge. |
| `primeShiftCount`, `InfinitelyOftenAtLeastPrimeShifts` | Reuse unchanged | Target of the universal modified sieve. |
| `Maynard.ImprovedGPY.Positivity` generic excess lemmas | Reuse unchanged | The finite positivity implication is independent of dimension and candidate. |
| `Maynard.ImprovedGPY.SquareWeights`, `SieveSums`, `PreSieve` | Reuse with small adapters | Low-level finite algebra and CRT are generic; endpoint `[N,2N)` versus source `[x,2x]` must be explicit. |
| `Maynard.MaynardWeights` generic finite coefficients | Generalize/prove new support lemmas | Definition can evaluate any `F`, but many later support/asymptotic proofs assume the ordinary product cutoff and simplex. |
| `Maynard.Variational` cube/insertion/boundedness infrastructure | Reuse infrastructure | Define new `modifiedI/J/modifiedKAt`; do not identify them with `maynardI/J`. The existing file contains no `K`. |
| `Maynard.smallKCandidate`, `SmallK*`, `EngelsmaCandidate` | Specialized to `k=105` | Do not import into the H1236 analytic path. New 48-dimensional trial data are independent. |
| `Maynard.Concrete*`, `boundedGapsStatement_of_bombieriVinogradov_and_pnt` | Cannot be used for modified sieve | Hard-coded ordinary prime indicator, 105 tuple/candidate, and fixed 600 conclusion. |
| `unconditional_ordinaryPrimeNumberTheorem` | Adapter/basic lemma | Useful for elementary prime-counting limits, insufficient for Harman five-prime mass without substantial new work. |
| `Maynard.unconditional_bombieriVinogradov` / `hasPrimeLevel` | Small adapters for fixed prime levels only | Can supply fixed-`θ` prime-prefix distribution. It cannot supply bilinear distribution, generated-term membership, or interval-SW for the negative Type-II branch. |
| `BoundedGaps.Proof.MainTheorem` | Preserve unchanged | It remains the unconditional H₁ ≤ 600 production theorem and must not enter the new analytic dependency path. |

## Mismatch register: manuscript versus dossier

1. **Different theorem:** SRC-S proves `H₁≤240` with `k=49`; SRC-D proposes `H₁≤236` with a new `k=48` tuple and explicitly conditions it on SRC-S Propositions 1–3.
2. **Different support and minorant:** SRC-S’s final p. 34 application uses one slice, `ε_s=.0075`, `δ=.028`, caps `.15/.17`, and `rho=1_P` with `c₁=c₂=0`. SRC-D uses two slices, limiting `ε_s=0` plus an existential enlargement, `δ=.014`, and a nontrivial Harman minorant with `c₂=24`.
3. **Negative branch:** SRC-S demands the impossible fourth capacity for
   negative `ω₀`; SRC-D replaces that range by prose invoking
   Bombieri--Vinogradov. The near-zero Type-IIc repair is quantified. The far
   claim is false for SRC-S's arbitrary Type-II class; it is repairable only
   for a narrower interval-SW/generated class not specified by SRC-D.
4. **`K` formula:** SRC-S’s printed `K` is ill-formed. SRC-D uses only consequences compatible with a thin full-dimensional reading. Milestone 3C reconstructs the same-coordinate formula uniquely from SRC-S Lemma 1 and Proposition 1; the packet's generic exact kernel instead chose an existential-projection convention, but no 236 computation evaluates it and its documentation notes that `c₂=0` made the choice irrelevant for 240.
5. **Tuple-universal conclusion:** SRC-S Proposition 1 headlines `H₁≤H(k)`; SRC-D states that every admissible `k`-tuple yields its own diameter. The stronger output is plausible from the proof but must be extracted and proved.
6. **Equality of `ξ₂,ξ₃`:** SRC-S Proposition 2 allows `ξ₂≤ξ₃`, but its proof text says `ξ₂<ξ₃`; SRC-D uses `ξ₂=ξ₃=4021/10000`.
7. **Zero-count cells:** SRC-S Definition 2 includes `m=0` or `m'=0`, while Proposition 3’s printed range begins at 1 despite its proof discussing `m+m'=0`. SRC-D includes zero counts in the 105-cell reduction.
8. **Distribution epsilon:** SRC-S Lemma 6 contains one `100ε_d` restatement, but its statement, construction, `50/55/54` downstream losses, Proposition 3 reuse, and all three predecessor versions force `52ε_d`. This is resolved as a typographical inconsistency; the dossier did not supply that resolution.
9. **Endpoint/support conventions:** SRC-S requires positive `ε_s` and half-open support bands. SRC-D performs finite integration on a limiting support with mixed weak/strict boundaries, then uses convergence; the equivalence is not in SRC-S.
10. **Nature of proofs:** SRC-S §3.3 gives amendments and says the underlying proofs span more than 50 pages; SRC-D correctly treats Propositions 1–3 as analytic input, but its phrase “complete relative to Analytic Input” must not be read as an independent proof of those amendments.
11. **Theorem typo:** SRC-S Theorem 1 defines `H₁` but prints `H_m≤240`; SRC-D consistently discusses `H₁`.
12. **Finite computation:** SRC-S’s final 240 computation is not the dossier’s Chebyshev/LP/Arb witness. All `73+8+24`, exact `I`, Arb `J`, `c₁`, and 48-tuple data are new dossier obligations.
13. **Universal Type-II quantifier:** SRC-S Proposition 3 says every
    `f∈H`, but Milestone 3F's balanced-character example is such an `f` and
    violates the conclusion on genuine cells. The intended concrete
    Harman/Heath--Brown provenance is absent from Definition 9.
14. **Alternative-sieve bridge:** SRC-S Proposition 2 imports the 2025
    construction, whose Lemma 19 invokes Baker--Weingartner Lemma 14.
    That lemma's arbitrary bounded test arrays do not visibly satisfy the
    SW-factor premise of the cited Type-II estimate, and no common
    exceptional-modulus argument is supplied.

## Human mathematical review required before Lean coding continues

1. Independently check the Milestone 3C source reconstruction of `K`, especially the passage from the sliced bilinear `K_i` to the global band formula and the null-boundary simplification. This is review of a resolved deduction, not a request for an author-supplied definition.
2. Independently review the counterexample, including its global SW proof
   and `q=3pr` genuine-cell strengthening; acknowledge that the printed
   Proposition 3 is false if the review confirms it.
3. Decide whether Proposition 2 is valid at `ξ₂=ξ₃`; audit the cited 2025 proof at the equality endpoint.
4. Correct the zero-count range and the final-column cap recurrence.
5. Independently review the proof-forced `52ε_d` correction before publication; formal work must use `58ε_d≤η` and the `55ε_d` fourth-bin margin.
6. Confirm Definition 2’s asymmetric `A_j-ε_s`/`A_{j'}+ε_s` bounds.
7. Approve the exact natural-scale/dyadic translation, the dyadic upper constant `K_q`, floor/ceiling endpoints, the moving logarithmic split, and every constant dependency in the Type estimates.
8. Approve the Fouvry--Radziwill Mellin transfer, its explicit logarithmic
   losses, and the required interval/twist-SW quantifier order.
9. Obtain a complete generated-term ledger and prove local SW for every
   direct, sifted, coupled, and Heath--Brown Type-II grouping used by the
   minorant.
10. Resolve the Baker--Weingartner arbitrary-test-array/common-exceptional-
    modulus bridge in the 2025 Lemma 19 chain.
11. Recursively audit the remaining Polymath, Baker--Irving, Maynard, and
    Stadlmann 2025 inputs; after the generated-class blocker, prioritize a
    vertical Type-III feasibility proof.
12. Check the two exceptional regions and all denominator lower bounds in the `c₁` rectangle majorant.
13. Independently replay/export full support LP witnesses and replace Arb `J` results with Lean-checkable rational certificates.
14. Choose the positive-enlargement route after an actual `ε_*` search; if none is certified, review every dominated-convergence boundary and domination lemma.
15. Approve the universal modified-sieve conclusion as prime shifts for an arbitrary admissible tuple, before specializing to the verified 48-tuple.

## Current gate decision

The `K` blocker and Lemma 6 constant blocker are closed. The negative split
and quantifier order are precise, and a generic sharp adapter is available
under interval-uniform SW. Nevertheless, the contract is **not authorized
for implementation as `AnalyticInput.lean`**: Proposition 3's printed
universal Type-II statement is false, and the sources do not supply the
generated minorant coefficient class, the membership/local-SW proof, or the
Baker--Weingartner bridge needed to narrow it safely. H236-SRC-030/031 are
the highest-priority statement/source blockers; Type III remains the largest
downstream analytic formalisation risk.

## Independent replacement route

Milestone 3H does not close or downgrade any gap in this register. It creates a
permanent pinned subproject, `Verification/PrimeGaps186Bridge/`, which derives
the current public H₁ ≤ 236 statement from the stronger conditional
`PrimeGaps186` liminf theorem. The terminal bridge depends on exactly
`kloosterman3_bound`, `kloosterman2_correlation_bound`, and
`physical_integral_bounds` beyond foundational axioms.

This bypass is independently auditable and reproducible, but it is not a
repair of Stadlmann Proposition 3. H236-SRC-030/031 and every human-review item
above remain open for the older path.

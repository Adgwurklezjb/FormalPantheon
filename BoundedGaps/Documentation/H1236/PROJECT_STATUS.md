# BoundedGaps project status

Status date: 2026-09-04. This is the authoritative entry point for the
completed project. Detailed source investigations remain in
[`Small_prime_gaps/`](Small_prime_gaps/), but their historical status should
be interpreted through the classification below.

## Executive summary

The repository contains three independent proof routes with different trust
boundaries:

1. FormalPantheon proves `H₁ ≤ 600` natively under Lean 4.32. This is the
   complete production result and has no project-specific axioms.
2. The Stadlmann-based `H₁ ≤ 236` work proves the statement layer, the
   48-element tuple, and the elementary bridges. Its analytic route is
   incomplete: the manuscript's universal Type-II clause is false for its
   printed coefficient class, and the required narrowed generated-term
   theorem is absent. This route is retained as a source audit and is
   superseded for obtaining a better numerical bound.
3. The isolated Lean 4.34 verifier imports a pinned `PrimeGaps186` theorem,
   proves that its liminf is the FormalPantheon liminf, and derives the public
   `H₁ ≤ 236` statement. This proof is kernel-checked conditional on exactly
   three explicit upstream inputs. The upstream `H₁ ≤ 186` theorem and the
   derived `H₁ ≤ 236` theorem are not unconditional.

## Route status

| Route | Formal status | Terminal result | Trust boundary |
|---|---|---|---|
| Native FormalPantheon `H₁ ≤ 600` | Complete native Lean result | `BoundedGaps.unconditional_boundedGapsStatement` | `propext`, `Classical.choice`, `Quot.sound` only |
| Stadlmann-based `H₁ ≤ 236` | Manuscript-audited but analytically incomplete; superseded | No terminal analytic Lean theorem exists | Printed universal Type-II clause refuted; generated-term/local-Siegel--Walfisz repair and other analytic/certificate work remain missing |
| PrimeGaps186 `H₁ ≤ 186` | Conditionally kernel-checked in the pinned upstream development | `PrimeGap186.primeGapLiminf_le_186` | Three upstream project axioms plus the foundational axioms |
| PrimeGaps186-derived `H₁ ≤ 236` | Independently verified conditional bridge | `BoundedGaps.H1236.boundedGapsStatement236_of_primeGaps186` | Exactly the same three upstream project axioms plus the foundational axioms |

“Unconditional” here means unconditional within the pinned Lean/Mathlib
dependency base: the kernel reports only its ordinary foundational axioms.
“Conditionally kernel-checked” means every implication after the named inputs
is checked by Lean, while those inputs remain axioms. “Numerically supported”
describes external evidence for an input and does not turn it into a Lean
proof. “Manuscript-audited but incomplete” means source claims and gaps were
analyzed without constructing a terminal theorem.

## Exact theorem chains

### Native FormalPantheon route

The terminal composition in `BoundedGaps/Proof/MainTheorem.lean` is:

```text
BoundedGaps.Maynard.unconditional_bombieriVinogradov
BoundedGaps.unconditional_ordinaryPrimeNumberTheorem
  -> BoundedGaps.Maynard.boundedGapsStatement_of_bombieriVinogradov_and_pnt
  -> BoundedGaps.unconditional_boundedGapsStatement
  -> BoundedGaps.boundedGapsStatement
     = arbitrarily large prime pairs with gap at most 600.
```

The Maynard composition internally uses the proved Bombieri--Vinogradov
route, ordinary PNT, exact `k=105` numerical certificate, admissible
105-element diameter-600 tuple, sieve positivity, and the tuple-to-gap and
liminf bridges. `REPRODUCING.md` records the detailed production dependency
map.

### Stadlmann-based 236 audit route

The implemented elementary tail is:

```text
BoundedGaps.InfinitelyOftenAtLeastPrimeShifts engelsmaTuple48 2
  -> BoundedGaps.H1236.boundedGapsStatement236_of_engelsmaTuple48_two_prime_shifts
  -> BoundedGaps.H1236.boundedGapsStatement236
  <-> BoundedGaps.H1236.primeGapLiminfStatement236
      by primeGapLiminfStatement236_iff_boundedGapsStatement236.
```

`engelsmaTuple48_card`, `engelsmaTuple48_admissible`, both endpoints, and its
upper bound 236 are proved. The required analytic antecedent is not proved.
There is no `AnalyticInput.lean`, no `conditional_H1_le_236` theorem, and no
project axiom standing in for the missing analysis.

The intended but incomplete upstream chain was:

```text
corrected Stadlmann Propositions 1--3
  + Type I/II/III distribution inputs
  + Harman minorant and mass theorem
  + support, I/J/K, and positive-enlargement certificates
  -> InfinitelyOftenAtLeastPrimeShifts engelsmaTuple48 2
  -> the implemented elementary tail above.
```

The first implication was deliberately not encoded because Proposition 3 is
false for the manuscript's printed universal Type-II class and no complete
generated-term/local-Siegel--Walfisz replacement is sourced.

### PrimeGaps186 replacement route

The pinned upstream and permanent bridge give:

```text
PrimeGap186.kloosterman3_bound
PrimeGap186.kloosterman2_correlation_bound
PrimeGap186.physical_integral_bounds
  -> PrimeGap186.dhl_40_2
  -> PrimeGap186.infinite_two_prime_translates_admissibleTuple
  -> PrimeGap186.primeGapLiminf_le_186
  -> BoundedGaps.H1236.primeGaps186_liminf_eq_formalPantheon
  -> BoundedGaps.H1236.primeGapLiminfStatement186_of_primeGaps186
  -> BoundedGaps.H1236.primeGapLiminfStatement236_of_primeGaps186
  -> BoundedGaps.H1236.primeGapLiminfStatement236_iff_boundedGapsStatement236
  -> BoundedGaps.H1236.boundedGapsStatement236_of_primeGaps186.
```

The equality step proves that upstream subtraction after coercion to `EReal`
equals FormalPantheon's natural subtraction followed by coercion. The
186-to-236 step is monotonicity of the bound. This route does not use the
48-tuple or any theorem from the Stadlmann analytic audit.

## Complete terminal axiom sets

The native terminal theorem prints:

```text
'BoundedGaps.unconditional_boundedGapsStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The pinned upstream terminal theorem prints:

```text
'PrimeGap186.primeGapLiminf_le_186' depends on axioms: [propext,
 Classical.choice,
 PrimeGap186.kloosterman2_correlation_bound,
 PrimeGap186.kloosterman3_bound,
 PrimeGap186.physical_integral_bounds,
 Quot.sound]
```

The permanent 236 terminal bridge prints:

```text
'BoundedGaps.H1236.boundedGapsStatement236_of_primeGaps186' depends on axioms: [propext,
 Classical.choice,
 PrimeGap186.kloosterman2_correlation_bound,
 PrimeGap186.kloosterman3_bound,
 PrimeGap186.physical_integral_bounds,
 Quot.sound]
```

The incomplete Stadlmann route has no terminal theorem whose axioms could be
printed. Its implemented elementary endpoint remains independently audited:

```text
'BoundedGaps.H1236.boundedGapsStatement236_of_engelsmaTuple48_two_prime_shifts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

This last theorem is an implication from an unproved analytic prime-shift
hypothesis; its clean axiom list does not establish that hypothesis.

## Versions and isolation

| Environment | Lean | Mathlib | Additional direct dependency |
|---|---|---|---|
| Main FormalPantheon project | `leanprover/lean4:v4.32.0` | `81a5d257c8e410db227a6665ed08f64fea08e997` | none |
| `Verification/PrimeGaps186Bridge/` | `leanprover/lean4:v4.34.0-rc2` | `bbcd1968ee6950abe88b85dba6995da346c4b2a8` | `openai/PrimeGaps186` at `61340d0b74163003b32756bb16e91d9209a5e330` |

Both `lake-manifest.json` files freeze their complete transitive dependency
sets. The nested verifier does not vendor the 210,000-line upstream file; it
fetches the exact commit and compiles the actual public FormalPantheon
statement modules from the parent checkout.

The bridge is isolated because `PrimeGaps186` requires Lean 4.34.0-rc2 while
the main project is pinned to Lean 4.32.0. A migration was tested only in a
clean temporary archive. With Lean 4.34.0-rc2 and Mathlib `bbcd1968...`, the
unchanged main sources failed across ten independent modules involving
measure/meromorphic APIs, arithmetic-function coercions, logarithmic
derivatives, `Finset.sup'`, and analytic-order APIs. This was not a small
auditable port, so the migration gate failed. No compatibility edits or
toolchain changes were applied to the active main project. The exact module
list is recorded in
[`Small_prime_gaps/PRIMEGAPS186_DURABLE_BRIDGE.md`](Small_prime_gaps/PRIMEGAPS186_DURABLE_BRIDGE.md).

## External assumptions and evidence

The preferred conditional route has exactly three unresolved inputs:

1. `PrimeGap186.kloosterman3_bound` — a published finite-field estimate that
   remains a Lean axiom.
2. `PrimeGap186.kloosterman2_correlation_bound` — a published finite-field
   correlation estimate that remains a Lean axiom.
3. `PrimeGap186.physical_integral_bounds` — 152 finite inequalities. The
   supplied Python/FLINT numerical certificate supports them, but the
   computation and the passage from computational enclosures to the physical
   integrals are not kernel proofs.

The first two inputs are mathematically sourced but not formalized. The third
is numerically supported but not discharged. No additional
project-specific axiom appears in the bridge's terminal dependency set.

The older Stadlmann route has a separate, substantially larger list of open
source, analytic, and certificate obligations. In particular, its printed
universal Type-II claim was refuted for the stated coefficient class. These
are documented in `Small_prime_gaps/GAP_REGISTER.md`; they are not hidden in
the three-input PrimeGaps186 trust boundary.

## Disposition of `AnalyticInput.lean`

`AnalyticInput.lean` was deliberately not created and is not planned as part
of this closed project. This is because the Stadlmann route has been
superseded by the independently verified PrimeGaps186 route, not because its
analytic gaps were resolved. Encoding the old proposed interface would still
risk freezing a false universal statement or an unproved generated-term
membership result as an assumption. The source audit remains available for
historical and future research.

## Reproduction

From the repository root, the native project workflow is:

```sh
# Optional on a fresh checkout: fetch Mathlib's pinned cache/dependencies.
lake exe cache get
lake build
lake env lean H1236StatementAudit.lean
lake env lean H1236TupleAudit.lean
lake env lean AxiomAudit.lean
```

The independent conditional bridge workflow is one command:

```sh
Verification/PrimeGaps186Bridge/verify.sh
```

That script enters its own project, refreshes only from its exact manifest and
commit pins, downloads the Mathlib cache, builds upstream `PrimeGaps186`,
builds the semantic bridge, and runs `IntegratedBridgeAudit.lean`.

Expected terminal outputs are the axiom lists above. Full commands, pins,
hashes, and build transcripts are in `REPRODUCING.md` and
[`Small_prime_gaps/PRIMEGAPS186_DURABLE_BRIDGE.md`](Small_prime_gaps/PRIMEGAPS186_DURABLE_BRIDGE.md).

## Final validation

The close-out reran both workflows on 2026-09-04:

- all three main-project audit files compiled and printed their unchanged
  axiom sets;
- the full Lean 4.32 `lake build` completed successfully with 4,434 jobs;
- `Verification/PrimeGaps186Bridge/verify.sh` retrieved the pinned state,
  built `PrimeGaps186` with 8,804 jobs, built the bridge with 8,809 jobs, and
  printed the five expected bridge axiom sets;
- the nested manifest hash remained
  `b4bc1f9d331347ba1a4a59690512a8f52596144bca6bacd7a2f76534702b9f09`;
- the changed-Lean-file scan found no `sorry`, `admit`, `sorryAx`, new axiom
  declaration, `native_decide`, `unsafe`, or `Challenge` import;
- `git diff --check` and explicit checks of the untracked deliverables found
  no whitespace errors.

The nested build emitted only deprecation warnings for the old spelling
`Nat.infinite_setOf_prime` in public modules compiled under Lean 4.34. These
are warnings, not errors, and no compatibility edit was made to the Lean 4.32
sources.

## Project closed

This project is closed with the following established results:

- a complete native Lean proof of `H₁ ≤ 600` under only the foundational
  axioms reported by Lean;
- kernel-checked definitions, tuple facts, and elementary bridges for the
  public `H₁ ≤ 236` statement;
- a permanent pinned proof that the conditional upstream `H₁ ≤ 186` theorem
  implies the current FormalPantheon `H₁ ≤ 236` statement, with exactly three
  explicit upstream assumptions.

It has not established an unconditional `H₁ ≤ 186` or `H₁ ≤ 236`, has not
proved the three upstream inputs, and has not completed or repaired the
Stadlmann analytic route. Future formalization of any remaining assumption is
a separate project rather than an unfinished requirement of this close-out.

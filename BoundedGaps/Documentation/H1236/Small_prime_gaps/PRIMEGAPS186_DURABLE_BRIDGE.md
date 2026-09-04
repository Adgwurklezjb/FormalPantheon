# Milestone 3H: durable PrimeGaps186 bridge

Date: 2026-09-04 (Australia/Sydney)

## Decision and status

The selected architecture is the permanent isolated verification subproject
at `Verification/PrimeGaps186Bridge/`. The main project remains on Lean 4.32.0
and Mathlib `81a5d257...`.

The subproject gives a one-command, kernel-checked proof of

```text
PrimeGap186.primeGapLiminf_le_186
  -> equality with the FormalPantheon consecutive-prime-gap liminf
  -> BoundedGaps.H1236.primeGapLiminfStatementAt 186
  -> BoundedGaps.H1236.primeGapLiminfStatement236
  -> BoundedGaps.H1236.boundedGapsStatement236.
```

The conclusion is conditional on exactly the three `PrimeGaps186` project
axioms. This route bypasses, and does not validate, the older Stadlmann
Proposition 3 argument.

## Preserved baseline

The active repository was initially:

```text
pwd
/Users/z2265001/Documents/Lean/PrimeGap236/FormalPantheon/BoundedGaps

git rev-parse HEAD
b0c0eff40d8785527440a04c0b6fbd1e30fc63a6

git status --short
?? Documentation/

cat lean-toolchain
leanprover/lean4:v4.32.0

lake env lean --version
Lean 4.32.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35
```

`git diff --check` printed nothing. The pre-existing untracked
`Documentation/` tree and all existing files were preserved.

The Milestone 3G report was read completely before implementation. Its
pre-Milestone-3H hash is:

```text
cc3e3b01eb3fc9d3a43bb18eacac65e725fce6286e20918bf192b0b7f69894ae  Documentation/H1236/Small_prime_gaps/PRIMEGAPS186_REPRODUCTION.md
```

The recovered temporary evidence had the following hashes:

```text
d671cc717097f4d3f275b9ed85ad6e9471f9054d9ff14936b9db66b462de129f  CurrentCompatibility.lean
1ce118606474f8f1303a2796267c1846e14dc5a5b26b393ab6b377eda2ef1cf9  IntegratedBridge.lean
a7d88b88dbe18b0aa4305fee42894b6514aa05edb2a60995823ac12d04833a05  IntegratedBridgeAudit.lean
```

Those files were inspected but not made dependencies of the durable result.
The permanent proof was reconstructed from the current public declarations
and the pinned upstream theorem.

## Why direct integration was rejected

A clean archive copy of the current commit was made under `/tmp`. Only in that
copy, the toolchain was changed from

```text
leanprover/lean4:v4.32.0
```

to

```text
leanprover/lean4:v4.34.0-rc2
```

and the Mathlib input was changed from `v4.32.0` / resolved revision
`81a5d257c8e410db227a6665ed08f64fea08e997` to exact revision
`bbcd1968ee6950abe88b85dba6995da346c4b2a8`.

Fresh dependency retrieval succeeded. The unchanged full-source command

```bash
lake build BoundedGaps
```

then produced independent errors in at least these ten production modules:

1. `BombieriVinogradov/Analytic/AdditiveLargeSieve/ConsecutiveIntervalKernel.lean`
   (`dsimp` no longer closes two embedding applications);
2. `BombieriVinogradov/Analytic/GoldfeldPlateauMellin.lean`
   (`MeromorphicOn`/`.meromorphicOn` API no longer found);
3. `BombieriVinogradov/Analytic/GoldfeldCoefficient.lean`
   (arithmetic-function coercion simplification no longer closes);
4. `BombieriVinogradov/Analytic/QuadraticZetaConvolutionSquare.lean`
   (`ZeroHom` versus `ArithmeticFunction` elaboration failures);
5. `BombieriVinogradov/Analytic/LocalLogarithmicResidue.lean`
   (function-eta form blocks a `logDeriv` rewrite);
6. `BombieriVinogradov/Analytic/FixedDiskLogDerivative.lean`
   (two `logDeriv` rewrites no longer match function-eta forms);
7. `BombieriVinogradov/Analytic/CenteredPrimitiveMaxima.lean`
   (`Finset.sup'` witness/result API mismatch);
8. `BombieriVinogradov/Analytic/VaughanSecondTermAggregate.lean`
   (`Finset.sup'` nonempty-witness elaboration mismatch);
9. `BombieriVinogradov/Analytic/DirichletPrimitiveShallowZeros.lean`
   (`analyticOrderNatAt` and `analyticOrderAt` APIs absent);
10. `BombieriVinogradov/Analytic/VaughanThirdTermSmallAggregate.lean`
    (`Finset.sup'` nonempty-witness elaboration mismatch).

There were also widespread deprecation warnings. The already-failed build was
stopped after the tenth independent source failure. No compatibility source
edit was attempted or applied, so there is no old/new source-patch table: the
migration gate required every unchanged module to build or a small, fully
auditable adaptation, and this failure surface was already broad. The active
toolchain, root Lake files, mathematical statements, and proofs were never
changed.

## Permanent isolated architecture

`Verification/PrimeGaps186Bridge/` contains:

- `lean-toolchain`: Lean `4.34.0-rc2`;
- `lakefile.toml`: exact direct pins for Mathlib and `PrimeGaps186`;
- `lake-manifest.json`: exact resolved revisions for every dependency;
- `IntegratedBridge.lean`: the semantic and theorem bridge;
- `IntegratedBridgeAudit.lean`: `#print axioms` for every bridge theorem;
- `verify.sh`: the one-command verifier;
- `README.md`: reproduction and trust-boundary documentation.

The subproject does not vendor `PrimeGaps186.lean`. It obtains the upstream
module from
`https://github.com/openai/PrimeGaps186.git` at exactly
`61340d0b74163003b32756bb16e91d9209a5e330`.

It also does not restate the current target. Its Lake library points two levels
up and imports the actual modules
`BoundedGaps.Statement`, `BoundedGaps.Proof.LiminfBridge`, and
`BoundedGaps.H1236.Statement` through the final import. Only this small import
closure is compiled under Lean 4.34; the main project is still built and
audited independently under Lean 4.32.

### Exact pins

| Package | Revision |
| --- | --- |
| `primeGaps186` | `61340d0b74163003b32756bb16e91d9209a5e330` |
| `mathlib` | `bbcd1968ee6950abe88b85dba6995da346c4b2a8` |
| `lean4export` | `cacf989bd75f608700820f6afc595f32e7a99a4d` |
| `Comparator` | `19e111e2141cf333c7daff0f64c5f24acc91dd2e` |
| `plausible` | `d9598f07b1bc701f1e3aae163d2681c1fd978793` |
| `LeanSearchClient` | `ba67e212be1197b84c1f1f6299488a10a3002713` |
| `importGraph` | `d8823026ac7ef130c253089d95685f9877b95323` |
| `proofwidgets` | `a8acbfd87375ff4abe14ce09db5b7664d383bc7f` |
| `aesop` | `18889deb9e83ea7420ef51c160d6f88552e744e3` |
| `Qq` | `507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3` |
| `batteries` | `7e23602c91bc04586b2b06de2708a041853e4681` |
| `Cli` | `ab3a82db9fea14cf0fd7f5a2de650f4b534640af` |

The generated manifest hash is:

```text
b4bc1f9d331347ba1a4a59690512a8f52596144bca6bacd7a2f76534702b9f09  Verification/PrimeGaps186Bridge/lake-manifest.json
```

Running the complete verifier left this hash unchanged. The retrieved
upstream `PrimeGaps186.lean` hash was
`fd7d9296871d276f7cd950ebf88d38627ff326abdf214a1facabc52fb6794d27`,
matching Milestone 3G.

## Exact semantic bridge

Upstream defines

```lean
Filter.liminf
  (fun n : ℕ =>
    (Nat.nth Nat.Prime (n + 1) : EReal) -
      (Nat.nth Nat.Prime n : EReal))
  Filter.atTop
```

whereas FormalPantheon defines `BoundedGaps.primeGap n` by natural-number
subtraction and then coerces it to `EReal` inside the same `liminf` and
`atTop` filter.

`primeGaps186_gapTerm_eq` proves the pointwise equality. Monotonicity of
`Nat.nth Nat.Prime` supplies

```text
Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime (n + 1),
```

so `Nat.cast_sub` identifies EReal subtraction of the two finite casts with
the cast of natural subtraction. This is propositional equality, not `rfl`.
Function extensionality and congruence of `Filter.liminf` then prove
`primeGaps186_liminf_eq_formalPantheon`.

The numeric step uses the kernel-checked fact `(186 : ℕ) ≤ 236` and
`EReal.natCast_le_iff`. The final theorem invokes the existing
`primeGapLiminfStatement236_iff_boundedGapsStatement236`; it does not reproduce
that equivalence.

The permanent declarations are:

```lean
BoundedGaps.H1236.primeGaps186_gapTerm_eq
BoundedGaps.H1236.primeGaps186_liminf_eq_formalPantheon
BoundedGaps.H1236.primeGapLiminfStatement186_of_primeGaps186
BoundedGaps.H1236.primeGapLiminfStatement236_of_primeGaps186
BoundedGaps.H1236.boundedGapsStatement236_of_primeGaps186
```

No theorem imports or mentions `Tuple48`, `engelsmaTuple48`, the proposed old
`AnalyticInput`, or any Stadlmann contract declaration.

## Reproduction

From the root of a fresh checkout containing these files:

```bash
Verification/PrimeGaps186Bridge/verify.sh
```

The executable script runs exactly:

```bash
cd Verification/PrimeGaps186Bridge
lake update
lake exe cache get
lake build PrimeGaps186
lake build IntegratedBridge
lake env lean IntegratedBridgeAudit.lean
```

The validation run began with an empty nested `.lake/`, fetched the exact
pinned sources, built upstream successfully in 541 seconds (8,804 jobs), built
the bridge successfully (8,809 jobs), and printed every theorem's axiom set.
The same script was then run as the public one-command interface and exited
successfully.

## Complete axiom output

```text
'BoundedGaps.H1236.primeGaps186_gapTerm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BoundedGaps.H1236.primeGaps186_liminf_eq_formalPantheon' depends on axioms: [propext, Classical.choice, Quot.sound]
'BoundedGaps.H1236.primeGapLiminfStatement186_of_primeGaps186' depends on axioms: [propext,
 Classical.choice,
 PrimeGap186.kloosterman2_correlation_bound,
 PrimeGap186.kloosterman3_bound,
 PrimeGap186.physical_integral_bounds,
 Quot.sound]
'BoundedGaps.H1236.primeGapLiminfStatement236_of_primeGaps186' depends on axioms: [propext,
 Classical.choice,
 PrimeGap186.kloosterman2_correlation_bound,
 PrimeGap186.kloosterman3_bound,
 PrimeGap186.physical_integral_bounds,
 Quot.sound]
'BoundedGaps.H1236.boundedGapsStatement236_of_primeGaps186' depends on axioms: [propext,
 Classical.choice,
 PrimeGap186.kloosterman2_correlation_bound,
 PrimeGap186.kloosterman3_bound,
 PrimeGap186.physical_integral_bounds,
 Quot.sound]
```

There is no additional non-foundational dependency.

## Trust boundary and route separation

### PrimeGaps186 route

The 236 conclusion is independently verified conditional on:

1. `PrimeGap186.kloosterman3_bound`;
2. `PrimeGap186.kloosterman2_correlation_bound`;
3. `PrimeGap186.physical_integral_bounds`.

The first two are published finite-field estimates that remain Lean axioms.
The Python/FLINT numerical certificate supports, but does not discharge, the
third axiom.

### Older Stadlmann route

The old conditional analytic contract is unchanged. Its printed universal
Type-II clause remains false at the stated generality, and the missing
generated-term/local-Siegel--Walfisz repair remains unresolved. The durable
bridge neither imports that route nor supplies evidence for Proposition 3.

### Unconditional FormalPantheon route

`BoundedGaps.unconditional_boundedGapsStatement` remains a separate Lean 4.32
theorem proving H₁ ≤ 600 with axiom set exactly
`[propext, Classical.choice, Quot.sound]`. The new bridge is not imported into
its production dependency path.

## Current-project regression validation

These commands were rerun from the Lean 4.32 project root after creating the
isolated artifact:

```bash
lake env lean H1236StatementAudit.lean
lake env lean H1236TupleAudit.lean
lake env lean AxiomAudit.lean
lake build
```

All four succeeded. The statement audit remained:

```text
'BoundedGaps.H1236.boundedGapsStatement236_contract' depends on axioms: [propext]
'BoundedGaps.H1236.boundedGapsStatement236_of_engelsmaTuple48_two_prime_shifts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BoundedGaps.H1236.primeGapLiminfStatement236_iff_boundedGapsStatement236' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All seven tuple declarations printed exactly
`[propext, Classical.choice, Quot.sound]`. The original final audit remained:

```text
'BoundedGaps.unconditional_boundedGapsStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The complete current build finished successfully with 4,434 jobs.

The changed-Lean-file search found no `sorry`, `admit`, `sorryAx`,
`native_decide`, `unsafe`, axiom declaration, `opaque`, `partial def`,
`extern`, `implemented_by`, `run_tac`, `ofReduceBool`, `trustCompiler`, or
import of `Challenge`. Neither bridge file mentions the Engelsma tuple or the
old analytic contract. The only upstream URL in configuration is immediately
paired with the exact 40-hex revision, and the manifest resolves every package
to an exact commit. Final `git diff --check` printed nothing and returned
success.

## Best next target for reducing conditionality

Among the three upstream inputs, `physical_integral_bounds` is the best next
target. It is a finite, computationally supported family and therefore offers
a plausible route through a kernel-checked rational/interval certificate
checker. The required work is still substantial: Lean must prove that the
computational enclosure forms majorize the physical integrals and verify all
finite contractions and directed-rounding steps. The two Kloosterman axioms
ultimately require deep ℓ-adic/cohomological results not currently available
as nearby Mathlib infrastructure, so they are less tractable as the next
engineering milestone.

## Final result

**Pass for the durable conditional bridge.** A fresh checkout can reproduce
the bridge with one documented command after network/toolchain availability.
The main project remains unchanged on Lean 4.32.0, and the old Stadlmann path
remains separately blocked.

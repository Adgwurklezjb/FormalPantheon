# Milestone 3G: independent `PrimeGaps186` reproduction and H₁ ≤ 236 bridge audit

Date: 2026-09-04 (Australia/Sydney)

## Conclusion

The exact upstream revision builds successfully in its pinned environment, and
its three terminal declarations depend on exactly the three documented project
axioms plus `propext`, `Classical.choice`, and `Quot.sound`.  A temporary
integration build proves in one Lean environment that

```text
PrimeGap186.primeGapLiminf_le_186
  -> BoundedGaps.H1236.primeGapLiminfStatement236
  -> BoundedGaps.H1236.boundedGapsStatement236.
```

This is a **conditional** verification route: it retains
`PrimeGap186.kloosterman3_bound`,
`PrimeGap186.kloosterman2_correlation_bound`, and
`PrimeGap186.physical_integral_bounds` as assumptions.  It does not validate or
repair the older Stadlmann Proposition 3 route.

The upstream module is not directly compatible with the current pinned Lean
4.32.0 / Mathlib revision.  Consequently no dependency, bridge module, or
toolchain change was made in the current repository.  The successful unified
bridge was checked only in an isolated temporary Lean 4.34.0-rc2 project.

## 1. Current repository state

Commands:

```bash
pwd
git status --short
git diff --check
git rev-parse HEAD
cat lean-toolchain
lake env lean --version
jq -r '.packages[] | [.name, .rev] | @tsv' lake-manifest.json
```

Recorded output:

```text
/Users/z2265001/Documents/Lean/PrimeGap236/FormalPantheon/BoundedGaps
?? Documentation/

b0c0eff40d8785527440a04c0b6fbd1e30fc63a6
leanprover/lean4:v4.32.0
Lean (version 4.32.0, arm64-apple-darwin24.6.0,
      commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35, Release)
```

`git diff --check` printed nothing and returned success.  The untracked
`Documentation/` tree was pre-existing and was preserved.

Current Lake dependency revisions:

| Package | Revision |
| --- | --- |
| mathlib | `81a5d257c8e410db227a6665ed08f64fea08e997` |
| plausible | `e12c1910fe855cbfc38803cd4e55543906d5fa62` |
| LeanSearchClient | `c5d5b8fe6e5158def25cd28eb94e4141ad97c843` |
| importGraph | `7e9612bf0b9ee66db3cb5b9988a35afc706f5a12` |
| proofwidgets | `6e311e2a844da9b2cc3971187df2fe0066947b93` |
| aesop | `a7dbf0c63b694e47f425f3dcddbc0e178bb432d3` |
| Qq | `38d591e778f100aec9762bb582f9c7f55f50e9dc` |
| batteries | `023ce7d62a0531e22a5331e20b587817a80d49ff` |
| Cli | `88679d088c9720c27ebdf2ba4dafe17341747f94` |

### Current statement and bridge declarations

The inspected current definitions are:

```lean
def BoundedGaps.H1236.boundedGapsStatementAt (C : ℕ) : Prop :=
  ∀ N : ℕ, ∃ p q : ℕ,
    N < p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q - p ≤ C

def BoundedGaps.H1236.boundedGapsStatement236 : Prop :=
  BoundedGaps.H1236.boundedGapsStatementAt 236

def BoundedGaps.primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

def BoundedGaps.H1236.primeGapLiminfStatementAt (C : ℕ) : Prop :=
  Filter.liminf (fun n : ℕ => (BoundedGaps.primeGap n : EReal))
    Filter.atTop ≤ (C : EReal)

def BoundedGaps.H1236.primeGapLiminfStatement236 : Prop :=
  BoundedGaps.H1236.primeGapLiminfStatementAt 236
```

The theorem
`BoundedGaps.H1236.primeGapLiminfStatement236_iff_boundedGapsStatement236`
equates the last two formulations.  The explicit contract theorem unfolds the
bounded statement to the strict inequalities displayed above.  The existing
tuple bridge is

```lean
BoundedGaps.H1236.boundedGapsStatement236_of_engelsmaTuple48_two_prime_shifts :
  InfinitelyOftenAtLeastPrimeShifts engelsmaTuple48 2 ->
    boundedGapsStatement236
```

That tuple bridge was inspected but is not used in the `PrimeGaps186` route.

## 2. Upstream source ledger and independent build

The repository was cloned into
`/tmp/primegaps186.m5G2tr/repo` and detached at exactly
`61340d0b74163003b32756bb16e91d9209a5e330`.  The supplied main paper was
downloaded to `/tmp/primegaps186.m5G2tr/short_gaps.pdf`.

Commands:

```bash
git clone https://github.com/openai/PrimeGaps186 /tmp/primegaps186.m5G2tr/repo
git -C /tmp/primegaps186.m5G2tr/repo checkout --detach \
  61340d0b74163003b32756bb16e91d9209a5e330
curl -L --fail --silent --show-error \
  https://cdn.openai.com/pdf/51126fac-1b68-4128-9666-c908bcc16033/short_gaps.pdf \
  -o /tmp/primegaps186.m5G2tr/short_gaps.pdf
shasum -a 256 PrimeGaps186.lean Challenge.lean formalization.yaml \
  lake-manifest.json lean-toolchain prime_gap_186_certificate.py \
  short_gaps_numerics.pdf
shasum -a 256 /tmp/primegaps186.m5G2tr/short_gaps.pdf
lake env lean --version
lake exe cache get
lake build PrimeGaps186
```

Hashes:

| File | SHA-256 |
| --- | --- |
| `PrimeGaps186.lean` | `fd7d9296871d276f7cd950ebf88d38627ff326abdf214a1facabc52fb6794d27` |
| `Challenge.lean` | `b99a403b1946547ef1926cd43ebce717640f7f76fa7e1f8f5a4b19ac2e53e1f0` |
| `formalization.yaml` | `8977ce060c1214afb4b71cb28a4c52d9d3db86d4d61183d0ece6ce57edf50752` |
| `lake-manifest.json` | `2cbec5d64ff57dbbbc5325ddd069aa9be155aae3e0b5bfdffab37c647edc1163` |
| `lean-toolchain` | `8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88` |
| `prime_gap_186_certificate.py` | `7f71bdefcfe3bb5ca76a143929b3cb3f4156c21dc483253cda3077420f1e5de4` |
| `short_gaps_numerics.pdf` | `79190b2ca18cb8aca0645a7bf97c1fb48e8984af4785cf18079d9b4f74c90031` |
| supplied `short_gaps.pdf` | `456f05e0a3ef589ebb0e9abcfd31f140f3c945adbf6950e00ef371a3c88b0930` |

Pinned environment:

```text
leanprover/lean4:v4.34.0-rc2
Lean 4.34.0-rc2, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d
mathlib bbcd1968ee6950abe88b85dba6995da346c4b2a8
```

Additional locked dependencies are `plausible d9598f0`,
`LeanSearchClient ba67e21`, `importGraph d882302`, `proofwidgets a8acbfd`,
`aesop 18889de`, `Qq 507746a`, `batteries 7e23602`, `Cli ab3a82d`,
`Comparator 19e111e`, and `lean4export cacf989` (full revisions remain in the
pinned manifest).

Results:

```text
lake exe cache get
  success: downloaded and decompressed 8787 cached files

lake build PrimeGaps186
  ✔ [8803/8804] Built PrimeGaps186 (566s)
  Build completed successfully (8804 jobs).
```

The source PDF metadata and rendered pages identify the documents as
*Improved short gaps between primes* (39 pages) and *Numerical certificate for
prime gaps at most 186* (23 pages).  Relevant source locations are the main
paper p. 1, Theorem 1.1 and Corollary 1.2; main paper printed p. 32 (PDF p. 33),
Lemma A.4 and (A.6); and numerical companion p. 21, Lemma 2.5, (2.33),
Corollary 2.6, and Remark 2.7.

### Comparator and numerical-certificate limitations

The Comparator instructions require `landrun`, `lean4export`, and `nanoda_bin`
on `PATH`.  None of `landrun`, `lean4export`, `nanoda`, `nanoda_bin`, or
`comparator` was available as a command after cache retrieval.  Although the
Comparator and lean4export source packages are locked Lake dependencies,
Nanoda and landrun were absent, so the Comparator workflow was not run and no
global tooling was installed.

The numerical certificate was not independently recomputed.  The host has
Python 3.13.3, whereas the recorded environment is Python 3.12.13, NumPy 2.2.6,
python-flint 0.9.0, and a custom corrected FLINT 3.6.0.  Both NumPy and `flint`
were absent.  The diagnostic

```bash
env -u PYTHONOPTIMIZE python3 -B prime_gap_186_certificate.py --help
```

failed immediately with `ModuleNotFoundError: No module named 'numpy'`.  No
replacement packages were installed.  In any event, the Python run would not
discharge the Lean numerical axiom.

## 3. Independent trust audit

`PrimeGaps186.lean` has 210,637 lines and imports only `Mathlib`.  The proof
module contains:

- no `sorry`, `admit`, or `sorryAx`;
- no `native_decide`, `unsafe`, `opaque`, `partial`, `extern`,
  `implemented_by`, `run_tac`, or `Lean.ofReduceBool` mechanism;
- no import or reference to `Challenge`;
- exactly three `axiom` declarations, at lines 147, 159, and 1055.

The two textual occurrences of the substring `admit` in the proof module are
ordinary English in documentation at lines 75648 and 75665.  They are not Lean
commands.

`Challenge.lean` separately imports only `Mathlib`, repeats the three declared
input axioms, and has exactly three intentional theorem `sorry` bodies at lines
954, 960, and 964.  `lakefile.toml` declares `Challenge` as a separate,
non-default library.  It is not imported by `PrimeGaps186.lean` and is not in
the terminal declarations' dependency paths.

### Complete terminal axiom output

Command:

```bash
lake env lean PrimeGaps186AxiomAudit.lean
```

where the temporary audit file imported `PrimeGaps186` and printed the three
requested declarations.  Complete output:

```text
'PrimeGap186.dhl_40_2' depends on axioms: [propext,
 Classical.choice,
 PrimeGap186.kloosterman2_correlation_bound,
 PrimeGap186.kloosterman3_bound,
 PrimeGap186.physical_integral_bounds,
 Quot.sound]
'PrimeGap186.infinite_two_prime_translates_admissibleTuple' depends on axioms: [propext,
 Classical.choice,
 PrimeGap186.kloosterman2_correlation_bound,
 PrimeGap186.kloosterman3_bound,
 PrimeGap186.physical_integral_bounds,
 Quot.sound]
'PrimeGap186.primeGapLiminf_le_186' depends on axioms: [propext,
 Classical.choice,
 PrimeGap186.kloosterman2_correlation_bound,
 PrimeGap186.kloosterman3_bound,
 PrimeGap186.physical_integral_bounds,
 Quot.sound]
```

Thus the complete non-foundational dependency set is exactly the documented
three project axioms.

### Audit of the three project assumptions

1. `PrimeGap186.kloosterman3_bound` quantifies over every natural prime `p`
   through `[Fact p.Prime]`, every `c : ZMod p`, and assumes `c != 0`.  It bounds
   the norm of the normalized three-variable sum by `3`.  The normalization is
   division by `p`.  This matches the first estimate in main-paper Lemma A.4,
   (A.6).

2. `PrimeGap186.kloosterman2_correlation_bound` quantifies over every natural
   prime and all nonzero `A B : ZMod p`.  Its finite sum includes exactly those
   `t` with `t != 0` and `t != -1`, uses the two unnormalized `K₂` factors at
   `A/t` and `B/(t+1)`, and is bounded by `8 * p * sqrt p`.  This matches the
   second estimate of Lemma A.4, (A.6), including the normalization conversion
   discussed in its proof.  There is no extra `A != B` hypothesis in either
   statement.

3. `PrimeGap186.physical_integral_bounds` assumes two inequalities for every
   one of 17 and 35 outer rows, one inequality for every one of 7, 10, 11, and
   17 inner rows, and three cap bounds.  The source proves the list lengths
   `[17, 35, 7, 10, 11, 17]` and total 97 rows, so the axiom comprises
   `2 * 52 + 45 + 3 = 152` inequalities, of which 149 are physical-source
   upper inequalities plus the three cap bounds.  The three cap constants are
   exactly those in numerical-companion (2.33).  Remark 2.7 explicitly says
   that the computational forms majorize the physical source integrals but are
   not identified with them by definition.  Lean proves the later rational
   assembly, not the finite production contractions or Arb/FLINT evaluation.

The main paper presents the mathematical DHL[40,2] theorem and H₁ ≤ 186,
but it also states that the Lean formalization is conditional on the numerical
and finite-field inputs.  The checked Lean result is therefore manuscript- and
axiom-conditional, not unconditional.

### Open issues

The GitHub issues API was inspected on 2026-09-04.  Four issues were open:

| Number | Title | Mathematical or declaration content |
| --- | --- | --- |
| 4 | `I was here` | empty body |
| 3 | `Promise I was here first` | empty body |
| 2 | `i was also here` | body `twin` |
| 1 | `i was here` | empty body |

None mentions the proof source, the three terminal declarations, their types,
or their assumptions.  No currently open issue affects this audit conclusion.

## 4. Exact statement compatibility

| Feature | Upstream | Current FormalPantheon | Result |
| --- | --- | --- | --- |
| Consecutive primes | `Nat.nth Nat.Prime n` and `Nat.nth Nat.Prime (n+1)` | exactly the same | equal indexing |
| Index base/offset | zero-based `Nat.nth`; successor `n+1` | exactly the same | no reindexing |
| Subtraction | subtraction after coercion to `EReal` | natural truncated subtraction, then coercion to `EReal` | not definitionally equal; propositionally equal |
| Limit operation | `Filter.liminf` | `Filter.liminf` | identical |
| Filter | `Filter.atTop` on `ℕ` | `Filter.atTop` on `ℕ` | identical |
| Bound | `(186 : EReal)` | `(236 : EReal)` | monotonicity via `186 ≤ 236` |
| Public bounded gaps | upstream terminal theorem is the liminf inequality | `∀ N, ∃ p q, N < p < q`, both prime, `q-p ≤ 236` | current proved iff supplies exact strict form |

For each `n`, monotonicity of `Nat.nth Nat.Prime` gives

```text
Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime (n + 1).
```

Therefore `Nat.cast_sub` proves

```lean
(Nat.nth Nat.Prime (n + 1) : EReal) -
    (Nat.nth Nat.Prime n : EReal) =
  ((Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : ℕ) : EReal).
```

Function extensionality and congruence of `Filter.liminf` give equality of the
two liminf values.  This is a genuine proof; `rfl` does not prove the displayed
term equality.  After normalizing the subtraction, the current
`BoundedGaps.primeGap` definition is definitionally equal (`rfl`) to the
right-hand sequence.

The upstream auxiliary prime-pair lemma uses a non-strict lower bound `N ≤ p`,
but that lemma is not needed for this bridge.  The terminal liminf statement is
transported directly, and the already-checked current equivalence produces the
strict public condition `N < p`.  There is therefore no interval-endpoint gap.

No claim about equality, inclusion, or specialization of the upstream
40-element tuple and the current Engelsma 48-element tuple is used or needed.

## 5. Compatibility gate and checked bridge

### Direct current-toolchain test: failed

Command:

```bash
lake env lean -DmaxErrors=20 \
  /tmp/primegaps186.m5G2tr/repo/PrimeGaps186.lean
```

run from the current FormalPantheon root under Lean 4.32.0 / Mathlib
`81a5d257...` failed.  The first errors are in the exact upstream source:

```text
PrimeGaps186.lean:1585:17: unknown identifier
  MeasureTheory.integrableOn_comp_log_Ioi
PrimeGaps186.lean:1655:8: unknown identifier LSeries_def₀
PrimeGaps186.lean:2096:13 and :31: unknown identifiers
  ite_eq_right and ite_eq_left
PrimeGaps186.lean:2668:75: Measure.map_smul API application type mismatch
PrimeGaps186.lean:3348:2: failed to synthesize IsProbabilityMeasure
```

Further measure-map API mismatches and missing identifiers followed; the
diagnostic stopped at the requested maximum of 20 errors at line 5708.  This
is sufficient to close the direct-compatibility gate.  The current
`lakefile.toml`, manifest, toolchain, and Lean source files were not changed.

### Isolated unified integration: passed

After the exact upstream build and hash audit, a temporary target was added
only inside the disposable clone.  It used upstream's pinned environment,
made the unchanged current `BoundedGaps/` source tree visible as a library, and
compiled a bridge importing both `PrimeGaps186` and
`BoundedGaps.H1236.Statement`.

The bridge proves:

```lean
BoundedGaps.H1236.primeGaps186_liminf_eq_current :
  PrimeGap186.primeGapLiminf =
    Filter.liminf (fun n : ℕ => (BoundedGaps.primeGap n : EReal))
      Filter.atTop

BoundedGaps.H1236.primeGapLiminfStatement236_of_primeGaps186 :
  BoundedGaps.H1236.primeGapLiminfStatement236

BoundedGaps.H1236.boundedGapsStatement236_of_primeGaps186 :
  BoundedGaps.H1236.boundedGapsStatement236
```

The core implication is

```lean
have h186236 : (186 : ℕ) ≤ 236 := by omega
exact PrimeGap186.primeGapLiminf_le_186.trans
  (EReal.natCast_le_iff.mpr h186236)
```

after rewriting by the proved liminf equality.  The final theorem applies
`primeGapLiminfStatement236_iff_boundedGapsStatement236.mp`.

Command and result:

```text
lake build IntegratedBridge
  Built BoundedGaps.Statement
  Built BoundedGaps.Proof.LiminfBridge
  Built BoundedGaps.H1236.Statement
  Built IntegratedBridge
  Build completed successfully (8808 jobs).
```

Only deprecation warnings for `Nat.infinite_setOf_prime` appeared while the
unchanged current source was compiled on the newer Mathlib.

Complete bridge axiom output:

```text
'BoundedGaps.H1236.primeGaps186_liminf_eq_current' depends on axioms: [propext, Classical.choice, Quot.sound]
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

This is one kernel-checked proof path in the upstream environment.  It is not
a production module in the current 4.32.0 project.

## 6. Logical dependency chain and scope

The checked replacement route is:

```text
kloosterman3_bound
kloosterman2_correlation_bound
physical_integral_bounds
  -> PrimeGap186.dhl_40_2
  -> PrimeGap186.infinite_two_prime_translates_admissibleTuple
  -> PrimeGap186.primeGapLiminf_le_186
  -> proved equality with the current natural-gap liminf
  -> EReal order transitivity using 186 ≤ 236
  -> BoundedGaps.H1236.primeGapLiminfStatement236
  -> existing liminf/bounded-pair equivalence
  -> BoundedGaps.H1236.boundedGapsStatement236.
```

What this establishes:

- the exact pinned upstream conditional Lean proof reproduces;
- its conclusion has the same consecutive-prime liminf semantics as the
  current project;
- under the upstream three assumptions, it implies the current explicit
  H₁ ≤ 236 statement.

What it does not establish:

- an unconditional H₁ ≤ 186 or H₁ ≤ 236 theorem;
- a proof of any of the three upstream project axioms;
- a rerun of the Python/FLINT numerical certificate;
- Comparator/Nanoda reproduction;
- validation or repair of Stadlmann Proposition 3 or the older 236 analytic
  contract;
- a current-root import of upstream under Lean 4.32.0.

## 7. Existing repository regression checks

Commands:

```bash
lake env lean H1236StatementAudit.lean
lake env lean AxiomAudit.lean
lake build
```

All succeeded.  Exact audit output:

```text
'BoundedGaps.H1236.boundedGapsStatement236_contract' depends on axioms: [propext]
'BoundedGaps.H1236.boundedGapsStatement236_of_engelsmaTuple48_two_prime_shifts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BoundedGaps.H1236.primeGapLiminfStatement236_iff_boundedGapsStatement236' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BoundedGaps.unconditional_boundedGapsStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The full current build completed successfully with 4,434 jobs.  The original
unconditional H₁ ≤ 600 result remains unchanged and retains only the expected
foundational axioms.

## Final disposition

**Pass**: exact upstream conditional reproduction, trust audit, semantic
compatibility, and isolated unified implication to the current H₁ ≤ 236
statement.

**No production integration under the present pin**: direct compilation fails
against the current older toolchain, and upgrading it was explicitly out of
scope.  A future integration must either port `PrimeGaps186` to Lean 4.32.0,
upgrade the FormalPantheon project after a separate migration decision, or
consume a suitably packaged theorem artifact through another explicitly
audited compatibility mechanism.

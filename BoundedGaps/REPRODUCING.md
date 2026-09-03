# Reproducing the unchanged `H₁ ≤ 600` baseline

This audit was run from
`~/Documents/Lean/PrimeGap236/FormalPantheon/BoundedGaps` on 2026-09-03
(Australia/Sydney). The repository's tracked mathematical Lean sources were not
changed. `AxiomAudit.lean` was already present and was left unchanged.

## Exact commands

Run from the project root:

```sh
git rev-parse HEAD
git status --short
lake env lean --version
sed -n '1,240p' lake-manifest.json
sed -n '1,20p' lean-toolchain
shasum -a 256 AxiomAudit.lean
lake build
lake env lean AxiomAudit.lean
```

The suspicious-token searches were:

```sh
rg -n -i --glob '*.lean' --glob '!.lake/**' '\b(sorry|admit|native_decide|unsafe|opaque|axiom|axioms|sorryAx|implemented_by|run_tac|ofReduceBool|trustCompiler)\b' .
rg -n -i --glob '*.lean' --glob '!.lake/**' '^\s*(axiom|axioms|opaque|unsafe)\b' .
rg -n -i --glob '*.lean' --glob '!.lake/**' '\b(sorry|admit|sorryAx)\b' .
rg -n -i --glob '*.lean' --glob '!.lake/**' '\b(native_decide|unsafe|implemented_by|run_tac|ofReduceBool|trustCompiler)\b' .
rg -n -i --glob '*.lean' --glob '!.lake/**' '\bopaque\b' .
rg -n -i --glob '*.lean' --glob '!.lake/**' '^\s*(unsafe\b|partial\s+def\b|extern\b)|\b(implemented_by|run_tac|ofReduceBool|trustCompiler|native_decide)\b' .
```

Import reachability was checked separately from textual matching. The following
read-only script parses only project-local `import` lines and computes their
transitive closure from `BoundedGaps.Proof.MainTheorem`:

```sh
python3 - <<'PY'
from pathlib import Path
from collections import deque

modules = {}
for path in Path('.').rglob('*.lean'):
    if '.lake' not in path.parts:
        modules['.'.join(path.with_suffix('').parts)] = path

seen = {'BoundedGaps.Proof.MainTheorem'}
queue = deque(seen)
while queue:
    module = queue.popleft()
    path = modules.get(module)
    if path is None:
        continue
    for line in path.read_text().splitlines():
        if line.startswith('import '):
            dependency = line.split()[1]
            if dependency in modules and dependency not in seen:
                seen.add(dependency)
                queue.append(dependency)

print(f'project modules reachable from BoundedGaps.Proof.MainTheorem: {len(seen)}')
for path in [
    Path('AxiomAudit.lean'),
    Path('Comparator/Challenge.lean'),
    Path('BoundedGaps/BombieriVinogradov/Challenge.lean'),
    Path('BoundedGaps/BombieriVinogradov/Statement.lean'),
    Path('BoundedGaps/Maynard/ConcreteConditionalPNTIntegration.lean'),
    Path('BoundedGaps/Maynard/ConcreteS2GoodComplementMainLimit.lean'),
    Path('BoundedGaps/Maynard/ConcreteS2MainPNTComposition.lean'),
    Path('BoundedGaps/Maynard/ConcreteS2MainNumeratorLimit.lean'),
    Path('BoundedGaps/Maynard/VariationalBridge.lean'),
]:
    module = '.'.join(path.with_suffix('').parts)
    print(('reachable:     ' if module in seen else 'not reachable: ') + str(path))
PY
```

The output was:

```text
project modules reachable from BoundedGaps.Proof.MainTheorem: 614
not reachable: AxiomAudit.lean
not reachable: Comparator/Challenge.lean
not reachable: BoundedGaps/BombieriVinogradov/Challenge.lean
reachable:     BoundedGaps/BombieriVinogradov/Statement.lean
reachable:     BoundedGaps/Maynard/ConcreteConditionalPNTIntegration.lean
reachable:     BoundedGaps/Maynard/ConcreteS2GoodComplementMainLimit.lean
reachable:     BoundedGaps/Maynard/ConcreteS2MainPNTComposition.lean
reachable:     BoundedGaps/Maynard/ConcreteS2MainNumeratorLimit.lean
reachable:     BoundedGaps/Maynard/VariationalBridge.lean
```

This found 614 project modules in the transitive import closure. Import
reachability is deliberately not described as proof-term dependency: the
declaration dependency chain below was checked from the theorem bodies as well.

## Frozen versions and initial status

`git rev-parse HEAD`:

```text
ffbb65c21afc8a36ace67720f1b0df1c63d26bd1
```

`git status --short`, captured before this report was created:

```text
?? ../.DS_Store
?? AxiomAudit.lean
```

Thus there were no modified tracked files. The two entries were pre-existing
untracked files; the `.DS_Store` is outside this project root and
`AxiomAudit.lean` is the requested audit harness.

`lake env lean --version`:

```text
Lean (version 4.32.0, arm64-apple-darwin24.6.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35, Release)
```

The complete contents of `lean-toolchain` are:

```text
leanprover/lean4:v4.32.0
```

The `mathlib` entry in `lake-manifest.json` pins:

```text
url: https://github.com/leanprover-community/mathlib4.git
inputRev: v4.32.0
rev: 81a5d257c8e410db227a6665ed08f64fea08e997
```

No `lake update` or dependency-changing command was run.

The checksum recorded before verification was:

```text
edb49917c2928b728f4f3cab5f6fcc41ada4346d17a54e44d79f9dd832087fff  AxiomAudit.lean
```

## Build and axiom audit

`lake build` exited successfully with code 0. Its complete emitted output was:

```text
ℹ [4112/4434] Replayed BoundedGaps.Maynard.SimplexMoments
info: BoundedGaps/Maynard/SimplexMoments.lean:457:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
ℹ [4425/4434] Replayed BoundedGaps.Maynard.ConcreteS2GoodComplementMainLimit
info: BoundedGaps/Maynard/ConcreteS2GoodComplementMainLimit.lean:109:0: 'BoundedGaps.Maynard.tendsto_engelsmaMaynardS2GoodComplementMain_div_scale_of_pnt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
ℹ [4426/4434] Replayed BoundedGaps.Maynard.ConcreteS2MainPNTComposition
info: BoundedGaps/Maynard/ConcreteS2MainPNTComposition.lean:78:0: 'BoundedGaps.Maynard.tendsto_engelsmaMaynardS2Main_sub_goodComplementMain_div_scale_zero_of_pnt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: BoundedGaps/Maynard/ConcreteS2MainPNTComposition.lean:80:0: 'BoundedGaps.Maynard.tendsto_engelsmaMaynardS2Main_div_scale_of_pnt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
ℹ [4427/4434] Replayed BoundedGaps.Maynard.ConcreteS2MainNumeratorLimit
info: BoundedGaps/Maynard/ConcreteS2MainNumeratorLimit.lean:36:0: 'BoundedGaps.Maynard.tendsto_engelsmaMaynardS2Main_div_scale_of_pnt_eq_maynardNumerator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
ℹ [4428/4434] Replayed BoundedGaps.Maynard.ConcreteConditionalPNTIntegration
info: BoundedGaps/Maynard/ConcreteConditionalPNTIntegration.lean:55:0: 'BoundedGaps.Maynard.engelsmaSmallKCandidateNormalizedAsymptotics_of_primeLevel_and_pnt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: BoundedGaps/Maynard/ConcreteConditionalPNTIntegration.lean:57:0: 'BoundedGaps.Maynard.boundedGapsStatement_of_bombieriVinogradov_and_pnt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Build completed successfully (4434 jobs).
```

The `SimplexMoments.lean:457:4` message is an informational tactic suggestion,
not a build error.

`lake env lean AxiomAudit.lean` exited successfully with code 0. The complete
output of `#print axioms` was:

```text
'BoundedGaps.unconditional_boundedGapsStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There was no error and therefore no failing file or declaration. In particular,
the audited declaration does not depend on `sorryAx` or on a project-specific
axiom.

## Production declaration and module dependency summary

The final proof body in `BoundedGaps/Proof/MainTheorem.lean` directly uses three
proved declarations:

1. `BoundedGaps.Maynard.boundedGapsStatement_of_bombieriVinogradov_and_pnt`;
2. `BoundedGaps.Maynard.unconditional_bombieriVinogradov`;
3. `BoundedGaps.unconditional_ordinaryPrimeNumberTheorem`.

The relevant production paths are as follows. These are theorem-body paths and
the principal supporting modules, not claims that every declaration in an
imported module occurs in the final proof term.

### Final statement and the 105-element tuple

- `BoundedGaps/Statement.lean` defines `boundedGapConstant = 600` and the exact
  proposition `boundedGapsStatement`.
- `BoundedGaps/Foundations/Admissible.lean` defines the explicit list
  `engelsmaTuple` and proves `engelsmaTuple_card = 105`, every member is at most
  600, and `engelsmaTuple_admissible`.
- `BoundedGaps/Proof/TupleBridge.lean` proves that infinitely many translates
  having at least two prime shifts from this tuple imply
  `boundedGapsStatement`.
- `BoundedGaps/Proof/MainTheorem.lean` closes the final statement using the
  unconditional Bombieri--Vinogradov theorem, the ordinary PNT, and the
  conditional Maynard composition.

### Maynard sieve and asymptotic composition

- `BoundedGaps/Maynard/ImprovedGPY/Positivity.lean` contains the finite Maynard
  positivity step: positive `S₂ - ρS₁` forces enough prime shifts, and
  `boundedGapsStatement_of_engelsma_eventuallyPositiveSieveExcess` invokes the
  tuple bridge.
- `BoundedGaps/Maynard/ImprovedGPY/SieveSums.lean` gives the exact finite
  pre-sieved `S₁` and `S₂` identities.
- `BoundedGaps/Maynard/AsymptoticPositivity.lean` turns normalized `S₁`/`S₂`
  limits with positive margin into eventual positive sieve excess.
- `BoundedGaps/Maynard/ConcreteWeights.lean` instantiates that result with the
  Engelsma tuple and concrete Maynard weights.
- `BoundedGaps/Maynard/EngelsmaCandidate.lean` transports the `Fin 105`
  variational candidate to the explicit tuple.
- `BoundedGaps/Maynard/ConcreteAsymptotics.lean` combines the selected level,
  positive numerical margin, and concrete normalized limits.
- `BoundedGaps/Maynard/ConcreteConditionalPNTIntegration.lean` discharges those
  limits from a prime-level hypothesis and ordinary PNT and exports
  `boundedGapsStatement_of_bombieriVinogradov_and_pnt`.

### Numerical certificate

- `BoundedGaps/Maynard/SmallKCertificate.lean` stores the exact rational
  certified denominator, numerator, and ratio and proves positivity and ratio
  greater than four using kernel-checked `norm_num` proofs.
- `BoundedGaps/Maynard/SmallKGeneratedCertificate.lean` verifies the generated
  denominator data against the source polynomial data.
- `BoundedGaps/Maynard/SmallKNumeratorGeneratedEvaluation.lean` verifies the
  generated numerator and proves `smallK_ratio_gt_four`.
- `BoundedGaps/Maynard/Variational.lean`, `VariationalBridge.lean`,
  `VariationalNumeratorBridge.lean`, and `SmallKFaceMoments.lean` connect those
  rational identities to Maynard's analytic `I` and `J` functionals.
- `BoundedGaps/Maynard/SmallKVariationalConclusion.lean` proves the checked
  `M_105 > 4` conclusion, and `BoundedGaps/Maynard/LevelSelection.lean` combines
  it with Bombieri--Vinogradov to obtain the positive main-term margin.

### Bombieri--Vinogradov and ordinary PNT

- `BoundedGaps/BombieriVinogradov/StandardStatement.lean` defines the standard
  weighted Bombieri--Vinogradov proposition.
- The `BoundedGaps/BombieriVinogradov/Analytic/` subtree proves the analytic
  estimates. `Proof/WeightedMainTheorem.lean` exports
  `unconditional_weightedBombieriVinogradov`.
- `Analytic/WeightedPrimeLevel.lean` and `Proof/StandardToNatural.lean` convert
  the weighted theorem to `hasPrimeLevel`; `Proof/WeightedComposition.lean`
  packages that conversion; and `Proof/MainTheorem.lean` exports
  `BoundedGaps.Maynard.unconditional_bombieriVinogradov`.
- `BoundedGaps/PrimeNumberTheorem/Statement.lean`,
  `PrimeNumberTheorem/Analytic/PrimeCounting.lean`, and
  `PrimeNumberTheorem/Proof/MainTheorem.lean` provide the ordinary-PNT input
  used by the final composition.

## Suspicious-token results and classification

The complete output of the combined textual search was:

```text
./AxiomAudit.lean:3:#print axioms BoundedGaps.unconditional_boundedGapsStatement
./Comparator/Challenge.lean:54:  sorry
./Comparator/Challenge.lean:58:  sorry
./Comparator/Challenge.lean:62:  sorry
./Comparator/Challenge.lean:67:  sorry
./BoundedGaps/BombieriVinogradov/Challenge.lean:33:  sorry
./BoundedGaps/BombieriVinogradov/Challenge.lean:83:  sorry
./BoundedGaps/BombieriVinogradov/Challenge.lean:144:  sorry
./BoundedGaps/BombieriVinogradov/Statement.lean:13:this file asserts no axiom or theorem proving Bombieri--Vinogradov.
./BoundedGaps/Maynard/ConcreteConditionalPNTIntegration.lean:55:#print axioms
./BoundedGaps/Maynard/ConcreteConditionalPNTIntegration.lean:57:#print axioms boundedGapsStatement_of_bombieriVinogradov_and_pnt
./BoundedGaps/Maynard/ConcreteS2GoodComplementMainLimit.lean:109:#print axioms tendsto_engelsmaMaynardS2GoodComplementMain_div_scale_of_pnt
./BoundedGaps/Maynard/ConcreteS2MainPNTComposition.lean:78:#print axioms
./BoundedGaps/Maynard/ConcreteS2MainPNTComposition.lean:80:#print axioms tendsto_engelsmaMaynardS2Main_div_scale_of_pnt
./BoundedGaps/Maynard/ConcreteS2MainNumeratorLimit.lean:36:#print axioms
./BoundedGaps/Maynard/VariationalBridge.lean:10:they are the analytic obligations, not project axioms.
```

Classification:

- The four `sorry` hits in `Comparator/Challenge.lean` are the placeholders for
  `boundedGapsStatement_iff_consecutive`,
  `paperLiminfStatement_iff_consecutive`,
  `paperLiminfStatement_iff_boundedGapsStatement`, and
  `unconditional_boundedGapsStatement`. The file identifies itself as a
  standalone challenge and is not in the import closure of the production main
  theorem.
- The three `sorry` hits in
  `BoundedGaps/BombieriVinogradov/Challenge.lean` are the placeholders for
  `coprimeResidues_nonempty`, `unconditional_bombieriVinogradov`, and
  `unconditional_weightedBombieriVinogradov`. This standalone comparator
  challenge is also not in the production import closure.
- `AxiomAudit.lean:3` is the audit command itself. It imports the production
  theorem; the production theorem does not import the audit file.
- The four reachable Maynard files shown above contain six `#print axioms`
  commands. These are diagnostic commands, not declarations and not inputs to
  any proof term. Their outputs during `lake build` report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `BoundedGaps/BombieriVinogradov/Statement.lean:13` and
  `BoundedGaps/Maynard/VariationalBridge.lean:10` are words inside module
  documentation comments. Both files are reachable by imports, but these text
  matches are not declarations.
- No challenge, comparator, test, archive, or audit declaration is used by
  `BoundedGaps.unconditional_boundedGapsStatement`. The two challenge modules
  and `AxiomAudit.lean` were explicitly found to be outside the forward import
  closure.

The declaration-shaped search for `axiom`, `axioms`, `opaque`, or `unsafe`
returned no matches (exit code 1). The dedicated `opaque` search also returned
no matches. Thus there is no explicit project `opaque` declaration being used
to conceal a proof. Ordinary Lean `theorem` opacity is not an unchecked proof
mechanism: theorem bodies are elaborated and kernel-checked.

The `sorry`/`admit`/`sorryAx` search returned exactly the seven challenge-file
`sorry` lines listed above: there were no `admit` or textual `sorryAx` hits.
The native/unsafe search and the declaration-shaped search covering `unsafe`,
`partial def`, `extern`, `implemented_by`, `run_tac`, `ofReduceBool`,
`trustCompiler`, and `native_decide` both returned no matches (exit code 1).

## Conclusion

**PASS for the unchanged production `H₁ ≤ 600` baseline.** The complete build
finished successfully, the final declaration compiled, and its axiom audit is
exactly `[propext, Classical.choice, Quot.sound]`. No production declaration in
the checked theorem path uses `sorry`, `admit`, a project-specific axiom,
`native_decide`, an unsafe proof mechanism, or an explicit `opaque` proof
wrapper. The seven repository `sorry` occurrences are isolated in standalone
challenge/comparator modules and are not dependencies of the audited theorem.

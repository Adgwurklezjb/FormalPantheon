# PrimeGaps186 bridge verification

This is a pinned, cross-toolchain verification artifact for the conditional
implication

```text
PrimeGap186.primeGapLiminf_le_186
  -> BoundedGaps.H1236.primeGapLiminfStatement236
  -> BoundedGaps.H1236.boundedGapsStatement236.
```

It uses Lean 4.34.0-rc2 and Mathlib revision
`bbcd1968ee6950abe88b85dba6995da346c4b2a8`. The upstream dependency is
`openai/PrimeGaps186` at exactly
`61340d0b74163003b32756bb16e91d9209a5e330`.

The bridge imports the real public FormalPantheon modules from the parent
checkout. It does not copy the 210,000-line upstream source, use `/tmp`, or
alter the main project's Lean 4.32 dependency graph.

## One-command verification

From the root of a fresh BoundedGaps checkout, run:

```bash
Verification/PrimeGaps186Bridge/verify.sh
```

The script performs the following exact sequence:

```bash
cd Verification/PrimeGaps186Bridge
lake update
lake exe cache get
lake build PrimeGaps186
lake build IntegratedBridge
lake env lean IntegratedBridgeAudit.lean
```

The final command prints the complete axiom set for every bridge theorem.

## Trust boundary

The terminal result is conditional on exactly these upstream project axioms:

- `PrimeGap186.kloosterman3_bound`;
- `PrimeGap186.kloosterman2_correlation_bound`;
- `PrimeGap186.physical_integral_bounds`.

It also uses the standard foundational axioms `propext`,
`Classical.choice`, and `Quot.sound`. The two finite-field bounds are published
mathematical estimates that remain Lean axioms. The numerical certificate
supports, but does not discharge, `physical_integral_bounds`.

This artifact is an independent replacement route. It does not validate the
older Stadlmann Proposition 3 argument, whose universal Type-II clause remains
separately blocked. It also does not affect FormalPantheon's unconditional
H₁ ≤ 600 theorem.

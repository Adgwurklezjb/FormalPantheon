# Source ledger for the conditional H₁ ≤ 236 project

Status date: 2026-09-04. This is a source audit, not a proof of H₁ ≤ 236. “In cone” below means in the intended final *unconditional* dependency cone, after the item has been proved or checked in Lean.

Workspace baseline: Git commit `b0c0eff40d8785527440a04c0b6fbd1e30fc63a6`; `lean-toolchain` is `leanprover/lean4:v4.32.0`; `lake env lean --version` reports Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, on `arm64-apple-darwin24.6.0`. At entry, `Documentation/` was already untracked and there were no tracked changes. The root contained `lakefile.toml`, `lean-toolchain`, all three existing H1236 modules, and both audit files.

## Sources actually inspected

| ID | Source and version | Actual path | SHA-256 |
|---|---|---|---|
| SRC-D | *A Verification Dossier for a Computer-Assisted, Manuscript-Conditional Bound H₁ ≤ 236*, research draft dated 3 September 2026 | `Documentation/H1236/Small_prime_gaps/Small_Gaps_236_Conditional_Proof.tex` | `ac7108b6d04269fe422c8e1074e2e383f074119f5b8517679e6f72536324d8c2` |
| SRC-G | *Project Guideline for an End-to-End Lean 4 Formalisation of the Target Bound H₁ ≤ 236*, version 1.0, 3 September 2026 | `Documentation/H1236/Small_prime_gaps/Lean_Formalisation_Guideline_H1_236.tex` | `b338efcae8cbdae8cd36b672ac05f8081a00df87ba5ca2fde018b476aa1077dd` |
| SRC-S | Julia Stadlmann, *Bounded Gaps Between Primes*, arXiv:2608.31126v1, 31 August 2026, 34 pages | `Documentation/H1236/Small_prime_gaps/Stadlmann_2608.31126.pdf` | `4296e63a3028fcff62725c7e751811679cbfea78e4d4213486b2f9a3e81ee994` |
| SRC-P | Optional verification packet | `Documentation/H1236/Small_prime_gaps/Small_Gaps_236_Verification_Packet.tar.gz` | `f5ac2ae5b85e268056fcea3b4232b6525755e992054a556e416bdc885ac51764` |
| SRC-ST | TeX source of SRC-S, arXiv:2608.31126v1 | versioned arXiv source archive, `Bounded_Gaps_2.0.tex` | `c0d5d2317c77f4de7eacdef6e1d4b1eb6433e6240b5c09273b3d4eee99e6c3ba` |
| SRC-O1 | Julia Stadlmann, *On primes in arithmetic progressions and bounded gaps between many primes*, arXiv:2309.00425v1 | versioned arXiv source, `Primes_in_arithmetic_progressions.tex` | `5e72a44e3feabc970abbdb7f8d87448a677f23335fc15c88829a3d2dfe7457d7` |
| SRC-O2 | same, arXiv:2309.00425v2 | versioned arXiv source, `Primes_in_arithmetic_progressions_2.tex` | `85bebaccf3ad2b269cef1fd4489dc193f72e47b6ee67509c3a8dbc7b8dc9ecd8` |
| SRC-O3 | same, arXiv:2309.00425v3, the published predecessor cited by SRC-S | versioned arXiv source, `Primes_in_arithmetic_progressions.tex` | `60c0440f33d9cbf504470716491fb4d45b45b26d9a960c8e34ff2af500837a30` |
| SRC-E | D. H. J. Polymath, *New equidistribution estimates of Zhang type*, arXiv:1402.0811v3 | versioned arXiv PDF/source, `newgap.tex` | `fdffe1dfb7b820d8a45ecc0e07e2f7e17404e6e10b63db110c2d44afe42013ea` |
| SRC-FR | E. Fouvry and M. Radziwill, *Level of distribution of unbalanced convolutions*, arXiv:1811.08672, Ann. ENS 55 (2022), DOI 10.24033/asens.2501 | versioned arXiv source, `FouvryRadzi7.tex` | `6206814742ed079d75742556d0a214f3e8db97419aa813d4c0cb4e6acb052cb7` |
| SRC-BW | R. C. Baker and A. Weingartner, *A ternary Diophantine inequality over primes*, Acta Arith. 162 (2014), 159--196, Lemma 14 | primary journal PDF, pp. 178--179, equations (4.1)--(4.3) | inspected for the test-sequence hypotheses; not copied into the repository |

The PDF identity was checked from the rendered first page, not inferred from its filename: it displays the title and author above and the margin identifier `arXiv:2608.31126v1 [math.NT] 31 Aug 2026`. The dossier copy inside SRC-P has the same SHA-256 as SRC-D.

The manuscript in turn imports results from Maynard (Annals of Mathematics
181 (2015)), two D. H. J. Polymath papers, Baker--Irving, and Stadlmann's
2025 predecessor. For Milestone 3C, the relevant portions of the primary
[Polymath Research in the Mathematical Sciences paper](https://arxiv.org/abs/1407.4897),
arXiv:1407.4897v4, were inspected: Theorem 3.6 and Section 5.3. Milestone 3E
inspected Theorem 2.9 and the fine partition in SRC-E and compared all three
predecessor revisions for the Lemma 6 loss. Milestone 3F additionally
inspected SRC-FR's exact sharp-output conversion, all Type-II and Harman
coefficient passages in SRC-S/SRC-O3, Polymath's concrete Heath--Brown atoms,
and SRC-BW's arbitrary test-sequence premise. The inaccessible publisher
endpoint for the original BFI scan returned HTML rather than a PDF; no claim
below relies on an inferred BFI interval convention. See
`SHARP_OUTPUT_BV_RESOLUTION.md` for exact page, equation, source-line, and
quantifier details.

## Notation and quantifier conventions

There are four different small parameters in the sources and they must not be identified:

- `ε_s > 0`: enlargement in the support `T_k(δ,A,B,ε_s)`;
- `ε₀ > 0`: shrinkage in the relevant-modulus family `Q*`;
- `η = 10⁻¹⁰`: the fixed safety constant printed as `ϵ` in Proposition 3;
- `ε_d > 0`: the sufficiently small smoothing/dyadic loss used in the Type I/II/III modulus families.

For asymptotic statements below, `x → ∞` is the varying scale. The tuple, dimension, support parameters, and the exponent parameters are fixed unless a row expressly says they vary uniformly. Every `≪` must become an eventual inequality with a named constant and threshold.

## Definitions and abstract sieve

### L-S01 — support region

- **Source:** SRC-S Definition 1, pp. 3–4; SRC-D lines 166–218.
- **Complete statement:** Fix `k,s ∈ ℕ`, `δ>0`, `ε_s>0`, numbers `-ε_s=A₀<A₁<⋯<A_s<1/2-ε_s`, and caps `B_{j,m}` for `1≤j≤s`, `1≤m≤⌊1/δ⌋`, satisfying `δ<B_{j,m}≤B_{j,m+1}≤B_{j,m}+δ` whenever both columns occur. For `t∈[0,1]^k`, put `I(t)={i:t_i>δ}`. Then
  `T_k(δ,A,B,ε_s)` is the union over `j=1,…,s` of the points satisfying
  `Σ_i t_i ∈ [A_{j-1}+ε_s,A_j+ε_s)` and `Σ_{i∈I(t)}t_i≤B_{j,|I(t)|}`.
- **Proposed Lean declarations:** `H1236.SupportSliceData`, `H1236.supportRegion`.
- **Prerequisites:** finite sums; measurable half-spaces; floor/index conversion; boundary-null lemmas.
- **Uniformity/constants:** the support is fixed before `x→∞`; the source’s recurrence is undefined at the last matrix column unless caps are extended or the quantifier is restricted.
- **Classification/cone:** new reusable definition; ambiguous at the final cap column; in cone.

### L-S02 — relevant modulus cells and their union

- **Source:** SRC-S Definition 2, pp. 3–4.
- **Complete statement:** For `x>0`, `ε₀>0`, `1≤j,j'≤s`, and `0≤m,m'≤⌊1/δ⌋`, `Q(x;δ,A,B,ε_s,j,j',m,m',ε₀)` consists of integers `q∈[1,x]` admitting
  `q=e e' (∏_{i=1}^m f_i)(∏_{i=1}^{m'}f'_i)`, with every displayed factor in `[1,x]`, such that
  `log_x(∏f_i)≤(1-ε₀)B_{j,m}`,
  `log_x(∏f'_i)≤(1-ε₀)B_{j',m'}`,
  `log_x(e∏f_i)≤(1-ε₀)(A_j-ε_s)`,
  `log_x(e'∏f'_i)≤(1-ε₀)(A_{j'}+ε_s)`,
  `e e'` is `x^δ`-smooth, and every `log_x f_i,log_x f'_i≥δ`. The family `Q*` is the union of these cells over all `j,j',m,m'`.
- **Proposed Lean declarations:** `H1236.relevantModulusCell`, `H1236.relevantModuli`.
- **Prerequisites:** prime factors and smoothness; real logarithms; finite factor tuples; conversion from real `x` to natural dyadic endpoints.
- **Uniformity/constants:** membership depends on `x`; `j,j',m,m'` vary over finite ranges uniformly.
- **Classification/cone:** missing definition; in cone.

### L-S03 — exact equidistribution property

- **Source:** SRC-S Definition 3, p. 4, and Definition 7/equation (3.1), p. 12; SRC-D lines 132–136.
- **Complete statement:** For fixed support data and `f:ℕ×(1,∞)→ℂ`, for every `ε₀>0` and power `D>0`, there is a constant `C=C(D,ε₀,support)` (and, in an eventual Lean form, a threshold `X₀`) such that, uniformly for `x≥X₀` and `a∈ℤ` coprime to every prime `p≤x`,
  \[
  \sum_{\substack{q\in Q^*(x)\\q\ \mathrm{squarefree}}}
  \left|\sum_{x\le n\le2x\atop n\equiv a\ (q)}f(n;x)
  -\frac1{\varphi(q)}\sum_{x\le n\le2x\atop(n,q)=1}f(n;x)\right|
  \le C\frac{x}{(\log x)^D}.
  \]
  Definition 7 additionally requires `ε_d` to be sufficiently small as a function of the fixed exponent triple; a fixed positive slack is needed for uniformity over a set of triples.
- **Proposed Lean declarations:** `H1236.EquidistributedForRelevantModuli`, `H1236.EquidistributedOn`.
- **Prerequisites:** `relevantModuli`; finite complex sums; congruences; totient; an explicit big-O-to-eventual adapter.
- **Uniformity/constants:** `C,X₀` may depend on `D,ε₀` and fixed support/exponent data, but not on `x,a,q` or a support cell. Uniformity in moving exponent triples is available only after a proved common slack.
- **Classification/cone:** missing definition and analytic property; in cone.

### L-S04 — the `I` and `J` functionals

- **Source:** SRC-S Definition 5, pp. 4–5; SRC-D lines 552–565.
- **Complete statement:** For symmetric square-integrable `F` supported on `T_k`,
  \[
  I(F)=\int_{T_k}F(t)^2\,dt.
  \]
  For each `1≤r,r'≤s`, `J` integrates
  `F(t₁,…,t_{k-1},u)F(t₁,…,t_{k-1},v)` over the common coordinates and `u,v`, subject to
  `Σ_{i<k}t_i≤max(A_r-ε_s,A_{r'}-ε_s)`,
  `Σ_{i<k}t_i+u∈[A_{r-1}+ε_s,A_r+ε_s]`, and
  `Σ_{i<k}t_i+v∈[A_{r'-1}+ε_s,A_{r'}+ε_s]`; `J` is the sum over `r,r'`.
- **Proposed Lean declarations:** `H1236.modifiedI`, `H1236.modifiedJ`.
- **Prerequisites:** product Lebesgue measure, coordinate insertion, measurability and integrability of restricted products, finite sum/integral interchange.
- **Uniformity/constants:** no asymptotic variable; open versus closed band endpoints must be reconciled using null boundaries.
- **Classification/cone:** new definitions; `maynardI`/`maynardJ` are useful patterns but are not these functionals; in cone.

### L-S05 — the printed `K` functional

- **Source:** SRC-S Definition 5, p. 4, repeated in §5.1 p. 31; Lemma 1 pp. 5–8; Proposition 1 proof pp. 10–11; SRC-D lines 732–746; `K_FUNCTIONAL_RESOLUTION.md`.
- **Printed statement:** It sums over `r,r'` an integral of `F(t₁,…,t_k)^2 dt₁⋯dt_k`, with conditions involving both `t_k` and a free `t'_k`. No `dt'_k` occurs. Thus the printed expression is not a well-formed integral.
- **Resolved statement:** replace the free `t'_k` in the third domain condition by the already integrated `t_k`. Thus
  `K=Σ_{r,r'} ∫ F(t)^2`, over points for which the common-coordinate sum exceeds `max(A_r-ε_s,A_{r'}-ε_s)` and the same total `Σ_i t_i` lies in both indicated bands. It is a `k`-dimensional same-point square integral. Up to null endpoints, the double sum reduces to one thin-region integral per band.
- **Evidence:** Lemma 1 p. 6 defines `K_i(F,G;C)` as `∫ F(t)G(t) dt₁…dt_k` over `Σ_{s≠i}t_s>C`; equations (2.3)–(2.6) preserve that form; the finite negative-minorant term on p. 11 is `-c₂B_i(n)^2`; Polymath Theorem 3.6 evaluates that non-prime square by one integral per coordinate; and the matrix formula on p. 31 uses `G_a(t)G_b(t)dt₁…dt_k`. No step produces a second fibre variable.
- **Proposed Lean declarations:** `H1236.modifiedKRegion`, `H1236.modifiedKAt`, followed by coordinate-independence for symmetric `F`.
- **Prerequisites:** measurable-set and integrability facts, null band boundaries, coordinate symmetry, and the Proposition 1 main-term proof.
- **Classification/cone:** source defect uniquely resolved by its proof; definition still unimplemented; in cone.

### L-S06 — admissibility of the trial function

- **Source:** SRC-S Definition 5 pp. 4–5 and Proposition 1 p. 5; SRC-D lines 538–547.
- **Complete statement:** `F:(Fin k→ℝ)→ℝ` is invariant under every permutation of its coordinates, is measurable, vanishes pointwise off the support (boundary changes may instead be handled almost everywhere), has integrable square on the cube, and has all additional product/fibre integrability needed to define `J` and the corrected `K`. The dossier’s concrete `F` is a bounded, compactly supported, two-piece polynomial combination times `1_{T₀}`.
- **Proposed Lean declaration:** `H1236.ModifiedTrialAdmissible`.
- **Prerequisites:** support measurability and piecewise-polynomial measurability/boundedness.
- **Classification/cone:** definition and later finite/measure-theoretic proof required; in cone.

### L-P01 — Proposition 1, modified-sieve implication

- **Source:** SRC-S Proposition 1 p. 5, proved via Lemmas 1–2 and Polymath Theorem 3.6 on pp. 5–11; SRC-D Proposition “Imported sieve implication”, lines 127–153.
- **Complete statement:** Fix any `k`, valid support data, and `ρ:ℕ×(1,∞)→ℝ`. Suppose for all sufficiently large `x` and `n∈[x,2x]`: (i) `-c₂≤ρ(n;x)≤1_P(n)`; (ii) `ρ` satisfies L-S03; (iii) `ρ(n;x)≠0` implies every prime divisor of `n` exceeds `x^β`, for some `β>max_j B_{j,1}`; and (iv)
  `Σ_{x≤n≤2x}ρ(n;x)=(1-c₁+o(1))x/log x` as `x→∞`. If a trial function satisfying L-S06 has `I(F)>0` and
  \[
  \frac{k(1-c_1)J(F)-kc_2K(F)}{I(F)}>1,
  \]
  then the GPY weights are eventually positive and an admissible `k`-tuple has arbitrarily large translates with at least two prime shifts. Consequently its gap is at most its diameter. The manuscript states the weaker-looking numerical conclusion `H₁≤H(k)`; the tuple-universal prime-shift conclusion is used in its proof and must be stated and proved explicitly in Lean.
- **Proposed Lean declaration:** `H1236.infinitelyOftenAtLeastTwoPrimeShifts_of_modifiedSieve`.
- **Prerequisites:** support approximation by smooth product functions (Lemma 1), evaluation of modified `S₁,S₂` (Lemma 2), Polymath Theorem 3.6, pre-sieving/CRT, positivity, and the roughness inequality `β>max_j B_{j,1}`.
- **Uniformity/constants:** `k,H,support,ρ,F,c₁,c₂,β` fixed as `x→∞`; error bounds must be uniform in tuple coordinate, residue class, support slice, and all divisor tuples. The order is: choose data, choose small approximation `ε₀`, then choose constants/thresholds, then all large `x`.
- **Classification/cone:** analytic theorem requiring formalisation. Low-level FormalPantheon square weights and positivity are reusable, but this proposition is not present; in cone.

## Harman minorant

### L-P02 — Proposition 2

- **Source:** SRC-S Proposition 2 and proof, pp. 21–24; SRC-D lines 225–281 and 683–730.
- **Complete statement:** Given support data, suppose `ξ₁,ξ₂,ξ₃∈(0,1)` and
  `2ξ₁+3ξ₂<2`, `ξ₂≤ξ₃`, `ξ₁+9ξ₂<4`, `2ξ₁+ξ₂>1`, and `17ξ₂<7`. Suppose every member of the Type I/II/III class `H(ξ₁,ξ₂,ξ₃)` has L-S03. Put `β=1-2ξ₂` and define `ρ=1_P-Γ_A-Γ_B`, where
  `Γ_A(n;x)` counts prime factorizations `n=p₁p₂p₃p₄p₅` with
  `β<α₄<α₃<α₂<α₁<ξ₂`, `α₁+α₂<ξ₂`, `α₂+α₃+α₄>1-ξ₂`, `α₅>α₄`, and `p_i=x^{α_i}`;
  `Γ_B(n;x)` counts factorizations `n=p₂p₃p₄p₅p₆` with every `β<α_i<8ξ₂-3`, `α₂,α₄>α₃`, `α₂+α₄<ξ₂`, `α₃+α₄+α₅>1-ξ₂`, and `α₆>α₅`.

  Let `c₁=L_A+L_B`, where `L_A` is the integral of
  `[α₁α₂α₃α₄(1-α₁-α₂-α₃-α₄)]⁻¹` over
  `β<α₁<ξ₂`, `β<α₂<min(α₁,ξ₂-α₁)`, `β<α₃<α₂`, and
  `max(β,1-ξ₂-α₂-α₃)<α₄<min(α₃,(1-α₁-α₂-α₃)/2)`;
  and `L_B` is the integral of
  `[α₂α₃α₄α₅(1-α₂-α₃-α₄-α₅)]⁻¹` over
  `β<α₂<8ξ₂-3`, `β<α₃<min(8ξ₂-3,α₂)`,
  `max(α₃,β)<α₄<min(8ξ₂-3,ξ₂-α₂)`, and
  `max(β,1-ξ₂-α₃-α₄)<α₅<min(8ξ₂-3,(1-α₂-α₃-α₄)/2)`.
  Put `c₂=24` if `ξ₂>4/10`, and `c₂=0` otherwise. Then `ρ` obeys the pointwise bound, L-S03, the rough-support conclusion with exponent `β`, and the mass asymptotic of L-P01.
- **Proposed Lean declarations:** `H1236.harmanClass`, `H1236.harmanMinorant`, `H1236.harmanMinorant_spec`.
- **Prerequisites:** Buchstab identities and the cited proof of Stadlmann (2025) §4, the Type I/II/III results below, short-interval prime asymptotics for five prime factors, and proofs of the multiplicity bounds 4 and 20.
- **Uniformity/constants:** support and `ξ_i` fixed; the Type estimates must be uniform through all Buchstab regions and dyadic decompositions. The mass `o(1)` is for `x→∞`.
- **Classification/cone:** analytic theorem requiring formalisation; in cone
  only after correction. The proof text says `ξ₂<ξ₃` at p. 22 although the
  proposition says `ξ₂≤ξ₃`; this matters because the dossier uses equality.
  Milestone 3F adds a logically prior issue: Proposition 2 assumes
  distribution for the broad class `H`, but Proposition 3 is false for that
  class. The minorant proof must instead export every generated term and
  prove it belongs to a narrower local-SW class. Stadlmann 2025 Lemma 19's
  Baker--Weingartner route also lacks a displayed bridge from arbitrary test
  arrays to a common SW-controlled exceptional-modulus set.

### L-R01 — pointwise minorant bounds

- **Source:** SRC-S Proposition 2(1), pp. 22–24.
- **Complete statement:** `∃X₀ ∀x≥X₀ ∀n∈[x,2x], -c₂≤ρ(n;x)≤1_P(n)`. For the dossier parameters `c₂=24`.
- **Proposed Lean declaration:** `H1236.IsPrimeMinorant`.
- **Prerequisites:** exact definition of `Γ_A,Γ_B` and multiplicity counts.
- **Classification/cone:** part of L-P02; analytic/combinatorial theorem; in cone.

### L-R02 — rough support and cap separation

- **Source:** SRC-S Proposition 2(3) p. 22 and Proposition 1(3) p. 5; SRC-D equations (beta-c2) and (beta-slack), lines 271–281.
- **Complete statement:** Eventually, `ρ(n;x)≠0 → ∀p, p.Prime → p∣n → x^β<p`, with `β=1-2ξ₂`; Proposition 1 additionally requires `β>max_{1≤j≤s}B_{j,1}`. At the dossier values, `β=979/5000` and `max_jB_{j,1}=39/250`, giving exact slack `199/5000`.
- **Proposed Lean declarations:** `H1236.HasRoughSupport`, `H1236.h1236_beta_gt_oneCaps`.
- **Prerequisites:** factorization support of the minorant and exact rational arithmetic.
- **Classification/cone:** roughness analytic; comparison finite; in cone.

### L-R03 — mass asymptotic

- **Source:** SRC-S Proposition 2(4), pp. 22–23; SRC-D lines 687–728.
- **Complete statement:** As `x→∞`,
  `Σ_{x≤n≤2x}ρ(n;x) / (x/log x) → 1-c₁`, with `c₁=L_A+L_B` exactly as in L-P02.
- **Proposed Lean declaration:** `H1236.HasMinorantMass`.
- **Prerequisites:** prime-number theorem in the multi-prime Buchstab regions, boundary estimates, and evaluation of both exceptional-region integrals.
- **Uniformity/constants:** `ξ_i` fixed; any dyadic or short-interval error must be uniform across the compact integration regions.
- **Classification/cone:** missing analytic theorem. FormalPantheon’s ordinary PNT is not sufficient by itself; in cone.

### L-R04 — rational bound on `c₁`

- **Source:** SRC-D §“A rational upper bound for the minorant loss”, lines 683–730, based on SRC-S Proposition 2 p. 22.
- **Complete statement:** At `t=4021/10000`, `β=979/5000`, every denominator factor in both integrals is at least `β`, and rectangle-width bounds give
  `L_A≤75969140625/14389093733134384`,
  `L_B≤75969140625/899318358320899`, hence
  `c₁≤1291475390625/14389093733134384<8.976×10⁻⁵`.
- **Proposed Lean declaration:** `H1236.h1236_c1_le`.
- **Prerequisites:** the exact exceptional regions from L-P02; Tonelli/monotonicity; rational normalization.
- **Classification/cone:** finite analytic inequality requiring Lean proof and human check against the source domains; in cone.

## Distribution classes and estimates

### L-D00 — coefficient and Harman classes

- **Source:** SRC-S Definitions 6–7 pp. 12–13 and Definition 9 p. 21.
- **Complete statement:** A coefficient sequence has divisor/logarithmic growth. “At scale `N(x)`” means support in `[cN(x),CN(x)]` for fixed positive `c,C`. The Siegel–Walfisz property is uniform in `q,r,a` with error `≪_D τ(qr)^{O(1)}N(x)/log(x)^D`. Smoothness means `α(n;x)=ψ_x(n/N(x))` for a compactly supported smooth `ψ_x` whose derivatives have stated polylogarithmic bounds. `H(ξ₁,ξ₂,ξ₃)` is the union of:
  Type I: `α*β`, `MN≍x`, `β` smooth, `N=x^γ`, `γ≥ξ₁-η`;
  Type II: `α*β`, `MN≍x`, both Siegel–Walfisz, `ξ₂-η≤γ≤1-ξ₂+η`;
  Type III: `α*ψ₁*ψ₂*ψ₃`, all `ψ_i` smooth, `MN₁N₂N₃≍x`, `x^{1-2ξ₃-η}≤N_i≤x^{ξ₃+η}`, and `N_iN_j≥x^{1-ξ₃-η}` for `i≠j`.
- **Proposed Lean declarations:** `H1236.CoefficientSequence`, `H1236.AtScale`, `H1236.SiegelWalfisz`, `H1236.SmoothAtScale`, `H1236.HarmanClass`.
- **Prerequisites:** arithmetic convolution; derivative/smooth-cutoff API; asymptotic uniformity framework.
- **Classification/cone:** missing definitions; manuscript's `O(1)`
  exponents are not quantified, so an approved explicit interpretation is
  required. More seriously, this arbitrary Type-II class is too broad for
  Proposition 3: the Milestone 3F counterexample belongs to it. A separate
  generated minorant class with interval-SW data is required; in cone only
  after that correction.

### L-DBV — full-support BV, the refuted class, and the valid local-SW adapter

- **Source:** SRC-E discrepancy (1.1) p. 6, coefficient sequences and Siegel–Walfisz (2.4)–(2.5) p. 9, Theorem 2.9 p. 11, and the finer-than-dyadic proof of Lemma 2.7 pp. 15–16.
- **Exact source statement:** If `M,N≫1`, `MN≍x`, `N≥x^ε` for fixed `ε>0`, `α,β` are coefficient sequences at scales `M,N`, and `β` has Siegel–Walfisz, then for every fixed `A>0` there is a fixed `B>0` such that
  `Σ_{q≤x^(1/2)log(x)^(-B)} sup_{a∈(ℤ/qℤ)ˣ} |Δ(α*β;a(q))| ≪ x log(x)^(-A)`.
  Equation (1.1) sums over the **entire finite support** in both terms of `Δ`; it contains no interval parameter.
- **Comparison/result:** L-S03 instead applies `Δ` to
  `(α*β)1_[x,2x]`. A constructed pair of bounded, globally SW coefficient
  sequences has sharp discrepancy `Ω(x)` not only modulo 3, but after
  summing `q=3pr` over genuine squarefree nonzero cells. Thus the generic
  sharp theorem and Proposition 3's printed universal Type-II conclusion
  are false. Factor truncation is nonseparable and global SW is not
  hereditary.
- **Valid source-backed repair:** SRC-FR Definition 1, pp. 2--3, makes SW
  uniform on every dyadic interval. Its Corollary 1.1 is sharp in
  `x<mn≤2x`; pp. 25--26, equations (58)--(62), derive this from full-support
  Proposition 8.1 using a `log^{-R}` collar, a divisor bound, Mellin
  inversion, polylogarithmic truncation height, partial summation, and
  uniform SW for twists. The same argument transfers to Theorem 2.9 for a
  uniformly parameterized interval-SW class.
- **Required Lean declarations:** first prove a generated-term membership
  theorem for every Proposition 2 Type-II term. Then prove
  `H1236.IntervalSWSharpBilinearBV`, ordered: fixed support/product/growth/SW
  data and `ε`; `∀A`; choose smoothing/twist losses and `B,C,X₀`; only then
  quantify `x,M,N,α,β`, intervals, cells, moduli, and residues. The weakest
  application restricts to generated terms and exact squarefree cell
  moduli.
- **Classification/cone:** the generic adapter under interval-SW is proved
  at the mathematical level from SRC-E and SRC-FR. Its membership premise
  is not established for every actual Harman term, and the printed broad
  class is refuted; critical.

### L-DI1 — Type I, `γ≤1/2`

- **Source:** SRC-S Lemma 5 p. 13 and proof pp. 17–18, adapting Baker–Irving Lemma 5.
- **Complete statement:** If `f=α*β`, `β` is smooth at scale `N=x^γ`, `MN≍x`, `γ≤1/2`, and `3γ-12ω-3δ>1`, then for every sufficiently small `ε_d>0`, `f` has L-S03 over moduli `d≤x^{1/2+2ω}` possessing `r∣d` with `x^{γ-δ-3ε_d}<r<x^{γ-3ε_d}`.
- **Proposed Lean declaration:** `H1236.typeI_belowHalf`.
- **Prerequisites:** amended Polymath Theorem 5.8 (SRC-S Lemma 8), Polymath Corollary 4.16 inequality 2 (Lemma 9), Cauchy–Schwarz, dyadic decomposition.
- **Uniformity/constants:** uniform on triples with fixed positive slack in the strict inequality; `ε_d` chosen after the triple/slack and before `x`.
- **Classification/cone:** analytic theorem requiring formalisation and comparison with an unsupplied source; in cone.

### L-DI2 — Type I, middle and upper branches

- **Source:** SRC-S Lemma 5 p. 13 and proof p. 18.
- **Complete statement:** For `1/2<γ≤1/2+2ω+ε_d`, use a divisor in
  `(x^{1-γ-δ-3ε_d},x^{1-γ-3ε_d})` and require `68ω+14δ<1`. For `γ>1/2+2ω+ε_d`, all moduli `d≤x^{1/2+2ω}` are asserted admissible with no factorization condition, by Polymath pp. 21–22.
- **Proposed Lean declarations:** `H1236.typeI_middle`, `H1236.typeI_upper`.
- **Prerequisites/uniformity:** as L-DI1, plus the role reversal used to invoke Type IIa; endpoints must be assigned exactly.
- **Classification/cone:** analytic theorems requiring formalisation; in cone.

### L-DIIA — Type IIa

- **Source:** SRC-S Lemma 3 pp. 12–13 and proof pp. 15–16, adapting Polymath Theorem 2.8(iv).
- **Complete statement:** If `f=α*β`, `MN≍x`, `N=x^γ≤x^{1/2}`, `β` has Siegel–Walfisz, and
  `24ω+7δ-5γ<-2`, `8ω+3δ-γ<0`, then for sufficiently small `ε_d`, L-S03 holds for squarefree `d≤x^{1/2+2ω}` with a divisor `r` satisfying `x^{γ-3ε_d-δ}<r<x^{γ-3ε_d}`.
- **Proposed Lean declaration:** `H1236.typeIIa_distribution`.
- **Prerequisites:** L-D00, amended Lemma 8, and the unmodified final part of Polymath Theorem 2.8(iv).
- **Uniformity/constants:** uniform only after a fixed slack is supplied for both strict inequalities.
- **Classification/cone:** analytic theorem requiring formalisation; in cone.

### L-DIIB — Type IIb

- **Source:** SRC-S Lemma 4 p. 13 and proof pp. 16–17, adapting Polymath Theorem 2.8(ii).
- **Complete statement:** Under the same convolution assumptions, if
  `24ω+7δ-3γ<-1` and `8ω+3δ-γ<0`, L-S03 holds for `d≤x^{1/2+2ω}` having `r∣d` in `(x^{γ-3ε_d-δ},x^{γ-3ε_d})` and `u∣d/r` in `(x^{1/2-γ-2ω-6ε_d-δ},x^{1/2-γ-2ω-6ε_d})`.
- **Proposed Lean declaration:** `H1236.typeIIb_distribution`.
- **Prerequisites:** Lemmas 8–10, the second exponential-sum inequality, gcd summation, and the modified factorization independent of `q₀`.
- **Uniformity/constants:** fixed slack in both inequalities and uniform dyadic choices of `Q,R,U,V`.
- **Classification/cone:** analytic theorem requiring formalisation; in cone.

### L-DIIC — Type IIc

- **Source:** SRC-S Lemma 6 p. 13 and proof pp. 18–20, adapting SRC-O3 Theorem 1; source resolution in `NEGATIVE_OMEGA_SOURCE_RESOLUTION.md`.
- **Complete statement:** If `f=α*β`, `MN≍x`, `N=x^γ≤x^{1/2}`, `β` has Siegel–Walfisz, and
  `8ω+4δ+2γ<1`, `32ω+10δ-γ<0`, `48ω+16δ-4γ<-1`, then L-S03 holds over `d≤x^{1/2+2ω}` with factors `r,u,d₁` satisfying the three intervals printed in Lemma 6, with the third interval using **`52ε_d`**. This value is proof-forced: the identity `H=x^{ε_d}RQ²/(q₀M)` converts it to the predecessor's `N/(q₀²x^{50ε_d}H²)` range, shortening gives the printed `55ε_d`, and the subsequent substitution gives `54ε_d`. The isolated `100ε_d` at the proof opening is a typographical inconsistency; it would instead force unprinted losses `98/103/102`.
- **Proposed Lean declaration:** `H1236.typeIIc_distribution`.
- **Prerequisites:** the complete 2025 proof, modified `q₀`-dependent ranges, diagonal bounds (3.5)–(3.7), and all exponential-sum estimates used there.
- **Uniformity/constants:** uniform on a fixed-slack compact set of `(ω,γ,δ)` and through every dyadic/factorization choice. In the near-zero endpoint repair, the exact safety condition is `58ε_d≤η`; the fourth capacity is `8ω₀+55ε_d`.
- **Classification/cone:** analytic theorem requiring formalisation; the `52/100` source ambiguity is resolved in favor of 52; in cone.

### L-DIII — Type III

- **Source:** SRC-S Lemma 7 pp. 13, 20–21, adapting Polymath Theorem 2.8(v).
- **Complete statement:** If `f=α*ψ₁*ψ₂*ψ₃`, `MN₁N₂N₃≍x`, each `ψ_i` is smooth, each pair `N_iN_j≫x^{1-γ}`, each `N_i` lies between constant multiples of `x^{1-2γ}` and `x^γ`, and `28ω+9γ+8δ<4`, then L-S03 holds for `d≤x^{1/2+2ω}` having a divisor in
  `(x^{1/3+4δ/3-4ω/3-δ},x^{1/3+4δ/3-4ω/3})`.
- **Proposed Lean declaration:** `H1236.typeIII_distribution`.
- **Prerequisites:** Polymath Theorem 2.8(v) pp. 85–93, relaxed fixed factorization, Lemma 7.5 convergence, exponential sums and smooth dyadic partitions.
- **Uniformity/constants:** fixed positive slack in `28ω+9γ+8δ<4`, uniform over the three smooth sequences and dyadic scales.
- **Classification/cone:** analytic theorem requiring formalisation; probably the deepest unavailable leaf; in cone.

## Proposition 3, separated into all obligations

In L-C01–L-C09, set `ω(j,j')=(A_j+A_{j'})/2-1/4` and
`Ξ(B₁,B₂,m,m',δ)={y∈[δ,1]^{m+m'}:Σ_{i≤m}y_i≤B₁, Σ_{i>m}y_i≤B₂}`.

### L-C01 — Proposition 3 global Type I condition

- **Source:** SRC-S Proposition 3(I), p. 26, proof p. 28; SRC-D lines 251–269.
- **Statement:** `min(ξ₁-4A_s+2/3, 1/7-(34/7)A_s)-2η>δ`.
- **Lean name:** `H1236.Prop3Global.typeI`.
- **Prerequisites:** L-DI1/L-DI2; exact substitutions `δ*(γ)` in both branches.
- **Classification/cone:** finite rational check after analytic lemmas; in cone. Dossier slack: `2499997/15000000000` in the binding branch.

### L-C02 — Proposition 3 global Type II conditions

- **Source:** SRC-S Proposition 3(II), pp. 26–27, proof pp. 28–30.
- **Statement:** both
  `2-36A_s-13δ+100η≥0` and
  `min(ξ₂/10-(32/10)A_s+8/10, ξ₂/4+11/16-3A_s)-2η≥δ`.
- **Lean name:** `H1236.Prop3Global.typeII`.
- **Prerequisites:** L-DIIA/L-DIIB/L-DIIC and the factorization Lemmas 11–13.
- **Classification/cone:** finite rational check after analytic lemmas; in cone. Dossier slacks: `3000001/100000000`, `3049999/5000000000`, and `124999/5000000000`.

### L-C03 — Proposition 3 global Type III condition

- **Source:** SRC-S Proposition 3(III), p. 27, proof p. 30.
- **Statement:** `11/8-(7/2)A_s-(9/8)ξ₃-2η>δ`.
- **Lean name:** `H1236.Prop3Global.typeIII`.
- **Prerequisites:** L-DIII and Lemma 11.
- **Classification/cone:** finite rational check after analytic lemma; in cone. Dossier slack: `28187499/5000000000`.

### L-C04 — local condition (A), Type I

- **Source:** SRC-S Proposition 3(A), p. 27, proof equations (4.5)–(4.6) p. 28.
- **Statement:** For every `j,j',m,m'` and every `y∈Ξ`, there is a disjoint exhaustive partition `I₁⊔I₂=Fin(m+m')` with
  `Σ_{I₁}y_i≤ξ₁-2η` and `Σ_{I₂}y_i≤1/6-4ω(j,j')-2η`.
- **Lean name:** `H1236.Prop3Local.typeI`.
- **Prerequisites:** a finite packing certificate plus Lemma 11.
- **Classification/cone:** finite certificate obligation; in cone.

### L-C05 — local condition (B), Type IIa

- **Source:** SRC-S Proposition 3(B), p. 27, proof equation (4.7) p. 28.
- **Statement:** There is `I₁⊔I₂` with
  `Σ_{I₁}y_i≤2/5+(24/5)ω+(7/5)δ-2η` and
  `Σ_{I₂}y_i≤1/14-(24/7)ω-2η`.
- **Lean name:** `H1236.Prop3Local.typeIIa`.
- **Prerequisites/classification/cone:** finite packing certificate plus Lemma 11; in cone.

### L-C06 — local condition (C), Type IIb

- **Source:** SRC-S Proposition 3(C), p. 27, proof equation (4.8) p. 29.
- **Statement:** There is `I₁⊔I₂⊔I₃` with respective capacities
  `1/3+8ω+(7/3)δ-4η`,
  `1/10-(34/5)ω-(7/5)δ-4η`, and
  `1/35+(22/35)ω+(21/35)δ-4η`.
- **Lean name:** `H1236.Prop3Local.typeIIb`.
- **Prerequisites/classification/cone:** finite packing certificate plus Lemma 12; in cone.

### L-C07 — local condition (D), nonnegative Type IIc branch

- **Source:** SRC-S Proposition 3(D) pp. 27, 29–30, corrected by SRC-D lines 99–123 and 342–482.
- **Statement:** For every `0≤ω₀≤ω(j,j')` and
  `ξ₂-η≤γ≤1/3+8ω(j,j')+(7/3)δ+3η`, there is an exhaustive four-way partition with capacities
  `γ-2δ-8ω₀-η`, `1/2-γ-2ω₀-η`, `δ+4ω₀-η`, and `8ω₀`.
- **Lean name:** `H1236.Prop3Local.typeIIc_nonnegative`.
- **Prerequisites:** Lemma 13, L-DIIC, and all 105 finite support cases.
- **Uniformity/constants:** uniform in the full closed rectangle of `(ω₀,γ)`; equality at capacity boundaries is allowed.
- **Classification/cone:** analytic reduction plus finite certificate; in cone.

### L-C08 — negative `ω₀` repair

- **Source:** not a theorem in SRC-S; proposed in SRC-D lines 99–123
  and gap G2 lines 910–917. SRC-E Theorem 2.9 is full-support. SRC-FR
  pp. 25--26 supplies a sharp conversion under interval-uniform SW. See
  `SHARP_OUTPUT_BV_RESOLUTION.md`.
- **Required statement:** Split at the exact logarithmic cutoff. If the
  dyadic upper bound is `q≤K_q x^{1/2+2ω₀}`, put
  `κ_{B,K_q}(x)=(B log log x+log K_q)/(2 log x)`. For
  `ω₀≤-κ_{B,K_q}(x)`, apply `IntervalSWSharpBilinearBV` only to a proved
  generated minorant Type-II term and take the actual squarefree cell
  subset. For `-κ_{B,K_q}(x)<ω₀<0`, reuse the zero-face partition and
  Lemmas 13 and 6 with loss 52, after choosing `ε_d>0` with `58ε_d≤η` and
  a common threshold satisfying the `9ε_d` and `55ε_d` inequalities.
- **Why the printed branch fails:** the counterexample has full-support
  cancellation but sharp discrepancy `Ω(x)`, and its `q=3pr` strengthening
  lies in genuine nonzero squarefree cells. It is a member of Definition
  9's arbitrary Type-II class. Thus the printed Proposition 3 and the
  generic global-SW sharp theorem are false, not merely unsupported.
- **Available uniform slack:** the moving split and source-valid Type-IIc
  endpoint cover the exponent range, but only after a generated-term/local-
  SW theorem supplies the far branch. SRC-FR proves the adapter mechanism;
  it does not prove membership of Stadlmann's omitted minorant term list.
- **Proposed Lean declaration:** `H1236.negativeOmega_distribution`.
- **Prerequisites:** the generated minorant coefficient class and its
  complete membership/local-SW proof; `IntervalSWSharpBilinearBV`; exact
  dyadic/floor/ceiling normalization; the resolved Lemma 6 loss; and
  endpoint/moving-parameter lemmas.
- **Classification/cone:** the adapter and branch quantifier order are
  precise, but the source-faithful generated-term theorem is missing;
  critical; in cone only after Proposition 2/3 are narrowed and reproved.

### L-C09 — endpoint `ω₀=0`

- **Source:** SRC-D lines 108–122 and the closed rectangles in lines 444–482; manuscript Proposition 3(D) p. 27.
- **Statement:** Assign `ω₀=0` only to L-C07. Then the fourth capacity is zero, so `I₄` must be empty because every `y_i≥δ>0`; the remaining capacities are `γ-2δ-η`, `1/2-γ-η`, and `δ-η`. The support checker must cover this exact closed face, and L-DIIC must be valid at it.
- **Lean name:** `H1236.Prop3Local.typeIIc_zero`.
- **Prerequisites:** closed-boundary coverage by the finite certificate and analytic endpoint review.
- **Classification/cone:** finite certificate plus analytic endpoint obligation; in cone.

### L-C10 — local condition (E), Type III

- **Source:** SRC-S Proposition 3(E) p. 27 and proof equation (4.9) p. 30.
- **Statement:** There is `I₁⊔I₂` with
  `Σ_{I₁}y_i≤1-6ω-(3/2)ξ₃-2η` and
  `Σ_{I₂}y_i≤(5/2)ω+(3/8)ξ₃-2η`.
- **Lean name:** `H1236.Prop3Local.typeIII`.
- **Prerequisites/classification/cone:** finite packing certificate plus Lemma 11 and L-DIII; in cone.

### L-P03 — corrected Proposition 3 conclusion

- **Source:** SRC-S Proposition 3 pp. 26–30 plus proposed SRC-D branch repair.
- **Corrected target:** the printed conclusion for every
  `f∈H(ξ₁,ξ₂,ξ₃)` is refuted. A defensible replacement quantifies over the
  exact `GeneratedMinorantClass` whose members occur in Proposition 2 and
  proves L-S03 for them, with L-C08 using the local-SW far branch.
- **Proposed Lean declaration:**
  `H1236.equidistributed_generated_of_prop3_conditions`.
- **Prerequisites:** a complete proof that every minorant term is in the
  generated class; all distribution estimates L-DI1–L-DIII; factorization
  Lemmas 11–13; the corrected negative branch; finite union/error
  bookkeeping; and the missing zero-count case.
- **Uniformity/constants:** uniform across all cells and the compact exponent rectangles; all strict global inequalities need named positive slack before choosing `ε_d`.
- **Classification/cone:** the source statement is false as printed. The
  narrower replacement requires author/expert confirmation and a new proof;
  critical, and not yet safe to encode.

## The fixed H₁ ≤ 236 data and finite calculations

### L-N01 — numerical parameters

- **Source:** SRC-D lines 166–281.
- **Statement:** `k=48`, `δ=7/500`, `A₁=253/1000`, `A₂=129/500`, `ξ₁=759/2000`, `ξ₂=ξ₃=4021/10000`, `η=1/10¹⁰`, `β=979/5000`, `c₂=24`. Lower caps for counts `0,1,2,3,4,5,≥6` are `0,39/250,39/250,17/100,23/125,19/100,101/500`; upper caps are `0,153/1000,153/1000,167/1000,181/1000,19/100,19/100` with the last value repeated.
- **Proposed Lean declarations:** the `h1236*` constants and `h1236SupportData` in `H1236.Analytic.Parameters`.
- **Prerequisites:** rational-to-real coercions.
- **Classification/cone:** finite data; in cone.

### L-F01 — finite support certificates

- **Source:** SRC-D lines 283–501 and Appendix “Type-IIc exact-dual replay jobs”.
- **Statement:** Plateau merging reduces all cells to 105 unordered pairs. Exact order-statistic witnesses prove (A),(B),(C),(E) for all 105 and (D) for 73; eight stated adaptive arguments and 24 exact rational LP-dual jobs prove the rest of (D), over the closed nonnegative `(ω₀,γ)` rectangles. The split is exactly `105=73+8+24`.
- **Proposed Lean declarations:** `H1236.frontierReduction`, `H1236.allDirectSupportCases`, `H1236.allAdaptiveSupportCases`, `H1236.allLPSupportCases`, `H1236.allSupportCases`.
- **Prerequisites:** list packing, exact rational weak duality, complete certificate data, and sound reflective checkers.
- **Classification/cone:** finite certificate obligation. The packet logs and Python scripts are evidence/generators, not Lean proofs; in cone.

### L-F02 — concrete trial function

- **Source:** SRC-D lines 503–547 and coefficient appendix.
- **Statement:** `R=129/500`, `D=7/500`, `L=101/500`. Three profiles are degree-8 Chebyshev polynomials on `[0,D]`, degree-12 on `(D,L]`, and zero elsewhere, with every printed terminating coefficient interpreted exactly. With `c=(571087/10⁹,-12804621/125000000,1)`,
  `F(t)=1_{T₀}(t) Σ_{ℓ=1}^3 c_ℓ∏_{i=1}^{48}g_ℓ(t_i)`.
- **Proposed Lean declarations:** `H1236.profile`, `H1236.trialFunction`.
- **Prerequisites:** exact coefficient data, Chebyshev recurrence, support and regularity proofs.
- **Classification/cone:** finite witness plus measure-theoretic facts; in cone.

### L-F03 — exact `I` certificate

- **Source:** SRC-D lines 549–628; packet `analysis/exact_chebyshev_i_8_12.json` and generator.
- **Statement:** The six symmetric entries of `R⁻⁴⁸ I` are exact rational values from capped polynomial convolution; contraction by the exact vector gives a positive exact rational `cᵀÎc`, displayed approximately as `1.994852232725948450897686×10⁻¹¹⁰`.
- **Proposed Lean declaration:** `H1236.trial_I_certificate`.
- **Prerequisites:** exact rational polynomial integration/convolution and parsing or generated Lean arrays.
- **Classification/cone:** finite certificate obligation; in cone.

### L-F04 — interval `J` certificate

- **Source:** SRC-D lines 630–680; six `analysis/arb_chebyshev_j*_8_12.json` packet files.
- **Statement:** Exact rational planar cell geometry and 1024-bit outward-rounded Arb contractions enclose all six entries of `R⁻⁴⁹J`; contraction yields `cᵀĴc∈[1.6134397849×10⁻¹¹¹±8.12×10⁻¹²²]` and
  `48R(cᵀĴc)/(cᵀÎc)∈[1.0016199680±8.30×10⁻¹¹]`.
- **Proposed Lean declaration:** `H1236.trial_J_certificate`.
- **Prerequisites:** a proved rational interval/polynomial integration checker and the complete cell certificate.
- **Classification/cone:** finite certificate obligation; Arb output alone is not a Lean proof; in cone.

### L-F05 — `K(F;0)=0`

- **Source:** SRC-D lines 732–746.
- **Statement:** Under the resolved same-coordinate `K`, `F(t)≠0` in a band ending at `A_j` implies the common-coordinate sum is at most `A_j`, whereas the `K` region requires it to be strictly above that endpoint; hence `K(F;0)=0`.
- **Proposed Lean declaration:** `H1236.trial_K_zero`.
- **Prerequisites:** exact endpoint conventions and the band-partition/null-boundary lemmas.
- **Classification/cone:** statement fixed; elementary measure/support proof still missing; in cone.

### L-F06 — strict limiting crossing

- **Source:** SRC-D lines 667–755.
- **Statement:** Combining the lower endpoint of L-F04 with L-R04 and the positive exact denominator gives
  `48R(1-c̄₁)(cᵀĴc)/(cᵀÎc)≥1.0015300688390691785>1`.
- **Proposed Lean declaration:** `H1236.trial_crossing_at_zero`.
- **Prerequisites:** L-R04 and L-F03–L-F05, all checked with rational inequalities.
- **Classification/cone:** finite certificate obligation; in cone.

### L-F07 — passage to positive `ε_s`

- **Source:** SRC-D lines 757–777; SRC-G lines 699–723.
- **Statement:** With `F` fixed, as `ε_s→0+`, `I(F;ε_s)=I(F;0)` for the nested supports, `J(F;ε_s)→J(F;0)` by dominated convergence, and `K(F;ε_s)→0` by absolute continuity over shrinking strips. The strict limiting margin then gives `∃ε_s>0` satisfying the Proposition 1 ratio.
- **Proposed Lean declarations:** `H1236.modifiedJ_tendsto_zero`, `H1236.modifiedK_tendsto_zero`, `H1236.exists_positive_epsilon_crossing`.
- **Prerequisites:** the resolved same-coordinate `K`, almost-everywhere convergence, measurable boundary/null-set facts, a common integrable majorant, and positivity of `I`.
- **Classification/cone:** measure-theoretic theorem requiring formalisation. No explicit positive rational `ε_s` is certified in the supplied packet; in cone.

### L-T01 — 48-tuple and application

- **Source:** SRC-D lines 779–821; existing `BoundedGaps/H1236/Tuple48.lean` and `TupleBridge.lean`.
- **Complete statement:** The explicit 48-element finset contains `0,236`, every entry is at most 236, and it is admissible. If L-P01 supplies `InfinitelyOftenAtLeastPrimeShifts engelsmaTuple48 2`, then
  `boundedGapsStatement236`; the existing statement bridge then gives the equivalent liminf assertion.
- **Existing Lean declarations:** `engelsmaTuple48_card`, `engelsmaTuple48_admissible`, `engelsmaTuple48_sorted_bounds`, `boundedGapsStatement236_of_engelsmaTuple48_two_prime_shifts`, and `primeGapLiminfStatement236_iff_boundedGapsStatement236`.
- **Prerequisites:** L-P01 instantiated with the finite support/trial data.
- **Classification/cone:** already proved in FormalPantheon; reusable unchanged; in cone.

## Existing FormalPantheon results: exact reuse assessment

| FormalPantheon item | Assessment | Reason |
|---|---|---|
| `BoundedGaps.H1236` statement, tuple, tuple bridge, liminf bridge | Reuse unchanged | These are exactly the elementary output layers and contain no analytic assumption. |
| `Maynard.sieveWeightSum`, `primeWeightedSieveSum`, `sieveExcess`, generic positivity lemmas | Reuse unchanged or with namespace adapters | They are finite, tuple-generic, and already yield `InfinitelyOftenAtLeastPrimeShifts H 2` from eventual positive excess. |
| `exists_preSieveResidueClass`, square-divisor weights, finite sum expansions | Reuse substantial low-level parts | Tuple-generic, but modified support/minorant asymptotics still need new proofs. |
| `Maynard.maynardCubeOf`, coordinate insertion, integration boundedness patterns | Reuse as infrastructure | Useful measure API; existing `maynardI/J` are the only Maynard functional definitions found and are not Stadlmann’s modified `I/J/K`. There is no existing `K`. |
| `smallKCandidate`, certificates, `engelsmaTuple`, concrete asymptotics | Cannot reuse for the 236 crossing | Specialized to `Fin 105`, the 105-element diameter-600 tuple, ordinary simplex, and prime indicator. |
| `unconditional_ordinaryPrimeNumberTheorem` | Reuse only as a basic input | It is the inclusive natural-endpoint limit for prime counting; Proposition 2 needs multi-prime/short-interval Buchstab mass results not supplied by this theorem alone. |
| `Maynard.unconditional_bombieriVinogradov` | Adapter only for fixed prime levels | It proves prime-indicator distribution for every fixed `θ<1/2` at inclusive natural endpoints. It does not state L-S03 for `Q*`, bilinear convolutions, interval-SW, or the generated-term theorem required by L-DBV. |
| `boundedGapsStatement_of_bombieriVinogradov_and_pnt` | Not reusable for 236 | It is a fully concrete k=105/diameter-600 composition and returns the fixed 600 statement. |

## Verification packet inventory

SRC-P was listed with `tar -tzf`; it was not extracted into the repository. Top level: `Small_Gaps_236_Conditional_Proof.tex`, `Small_Gaps_Improvement_Investigation.md`, `analysis/` (154 members), and `tmp/primegaps_exact/` (92 members). File formats are Python (`.py`, 92), exact/interval data (`.json`, 24), replay logs (`.log`, 66), NumPy data (`.npz`, 32), Markdown (`.md`, 18), plus one TeX file and project metadata.

Later Lean certificate work will need, at minimum:

- support generators/checks `verify_final_support.py`, `verify_adaptive_hand_lemmas.py`, `typeiic_exact_dual_replay.py`, the 24 required `exact_*.log` jobs, and a new export containing full rational dual witnesses rather than only digests;
- trial data `two_piece_chebyshev_8_12.json`;
- exact `I` data/generator `exact_chebyshev_i_8_12.json`, `exact_chebyshev_i.py`;
- all six final `arb_chebyshev_j{00,10,11,20,21,33}_8_12.json` files and `exact_chebyshev_j.py`, to be converted to proof-producing rational certificates;
- `check_chebyshev_certificate.py` and `audit_bundle.py` only as external consistency checks;
- the bundled `tmp/primegaps_exact` source snapshot, especially `src/primegaps/distribution.py`, `integrals.py`, `certificate.py`, and tests, as generator provenance.

Milestone 3C found that `tmp/primegaps_exact/src/primegaps/integrals.py`
implements a `k`-dimensional **existential-projection** convention for the
printed `t'_k`: it bounds the common sum by the witness band's upper endpoint
without integrating the witness coordinate. `docs/section5-engine.md`
documents that convention and says it is immaterial for the published 240
certificate because `c₂=0`; `tests/test_exact_integrals.py` only checks that
chosen convention against small numerical quadratures. No 236 analysis script
calls this evaluator with the dossier trial data. The 236 packet uses only the
symbolic empty-region argument at `ε_s=0` and supplies neither a
positive-`ε_s` `K` value nor a quantitative enclosure. The saved convention
is therefore generator provenance, not the definition to formalize. Full
candidate comparison and member digests are in `K_FUNCTIONAL_RESOLUTION.md`.

Python, SciPy/HiGHS, FLINT, NumPy, and Arb may propose or reproduce data. Their successful execution is not a Lean theorem and none of their outputs may enter the final dependency cone without a proved Lean checker.

## Ledger conclusion

FormalPantheon already proves the public 236 statement interfaces, the exact
tuple facts, the tuple-to-gap bridge, the liminf equivalence, the ordinary
PNT, a fixed-exponent prime Bombieri--Vinogradov theorem, and much of the
ordinary finite Maynard machinery. It proves none of Stadlmann Propositions
1--3, none of the Type I/II/III estimates in their required generalized
form, no Harman minorant, and none of the new support/integral certificates.
The `K` and `52ε_d` source ambiguities are resolved and the near-zero
endpoint split is quantified. Milestone 3F proves that the far-negative
claim over Definition 9's arbitrary Type-II class is false. A source-backed
sharp adapter exists after adding interval-uniform SW, but the sources do
not prove this property for every term actually generated by Proposition 2
and expose an additional Baker--Weingartner bridge gap. Therefore H₁ ≤ 236
remains manuscript-conditional and the analytic-input bundle is not safe to
encode.

## Independent PrimeGaps186 replacement route

Milestone 3H adds a source-independent replacement route without changing any
entry above. `openai/PrimeGaps186` commit
`61340d0b74163003b32756bb16e91d9209a5e330` proves
`PrimeGap186.primeGapLiminf_le_186` conditional on its two finite-field axioms
and `physical_integral_bounds`. The permanent subproject
`Verification/PrimeGaps186Bridge/` imports that pinned theorem and the actual
FormalPantheon public H₁ ≤ 236 statement modules, proves equality of the
two liminf quantities, and derives `boundedGapsStatement236`.

This new route is not evidence for L-P01, L-P02, L-P03, any Type I/II/III
entry, or the negative-ω₀ repair. All older ledger classifications and
blockers remain unchanged. Full provenance, hashes, commands, and axiom output
are in `PRIMEGAPS186_REPRODUCTION.md` and
`PRIMEGAPS186_DURABLE_BRIDGE.md`.

# Milestone 3F checkpoints

Status date: 2026-09-04. This is a working research log, not a proof of
`H₁ ≤ 236` and not an analytic assumption.

## Checkpoint 0 - entry and independent audit launched

- **Stage:** initial workspace/diff audit and source reinspection.
- **Workspace:** `/Users/z2265001/Documents/Lean/PrimeGap236/FormalPantheon/BoundedGaps`.
- **Entry status:** `?? Documentation/`; `git diff --check` exited 0 with no
  output. The whole documentation tree was already untracked; no tracked
  modification was present.
- **Sources queued:** the local Stadlmann arXiv:2608.31126v1 PDF and TeX
  source, arXiv:2309.00425 versions, Polymath arXiv:1402.0811v3 and its
  cited antecedents, the conditional-proof dossier, guideline, and existing
  3E ledgers.
- **Claims under audit:** the `52ε′` resolution; the uniform
  Siegel-Walfisz status and `Ω(x)` calculation of the modulo-3 example; the
  actual Proposition 3 Type-II class; and whether any sharp-output,
  prefix-maximal, weighted, smooth, Perron, or rectangular theorem closes
  the far-negative branch.
- **Current best theorem:** unchanged provisionally from 3E:
  `SharpIntervalBilinearBV`; this is a target, not a sourced theorem.
- **Failed approaches:** none newly adjudicated at entry.
- **Files changed in this checkpoint:** this checkpoint log only.
- **Next action:** reconstruct sources locally, inspect the full proof paths,
  and independently verify the counterexample before accepting its use.

## Checkpoint 1 - counterexample survives and reaches genuine cells

- **Stage:** completed independent audit of the Milestone 3E example and
  strengthened it to the actual nonzero-cell modulus family.
- **Sources inspected:** Stadlmann Definition 2 (relevant moduli), Definition
  3 (sharp discrepancy), Definition 9 (the Harman class), and Proposition 3;
  Polymath Definition 2.5 and Theorem 2.9.
- **Claims proved:** for `x=T^2`, `60 | T`, the two balanced block sequences
  `alpha=t*chi_3` and `beta=s*chi_3` are bounded, dyadically supported, and
  uniformly Siegel-Walfisz with error `O(tau(qr))`; their complete-support
  discrepancy at modulus 3 is exactly zero, while their `[x,2x]` discrepancy
  is `-(2/9)c_h*x+O(sqrt x)`, where
  `c_h=log((1+h/2)^2/(1+h))>0`.
- **Stronger source-level result:** take distinct primes
  `p,r in [x^theta1,x^theta2]` and `q=3pr`, with
  `delta<theta1<theta2<min((1-epsilon0)B_(1,1),
  (1-epsilon0)(A_1-epsilon_s),1/4)`.  These are squarefree members of a
  genuine `m=m'=1` cell.  Uniformly,
  `Delta_q=-c_h*x*phi(q)/q^2+O(sqrt(x)*tau(q))`; Mertens' theorem over the
  two prime bands gives a total `Omega(x)`.  Thus the problem is not confined
  to the manuscript's separately ambiguous zero-count cells.
- **Claim refuted:** `SharpIntervalBilinearBV` with the same arbitrary
  coefficient/Siegel-Walfisz hypotheses as Polymath Theorem 2.9 is false.
  Stadlmann Proposition 3 is also false for its universally quantified
  Type-II class as printed.
- **Files changed:** this checkpoint log only.
- **Next action:** reconstruct the concrete Harman/Heath-Brown atoms and test
  whether a strictly narrower interval-hereditary class repairs the proof.

## Checkpoint 2 - a valid generic adapter with an extra local hypothesis

- **Stage:** audited Polymath's finer-than-dyadic proof and formulated the
  support mechanism it actually uses.
- **Sources inspected:** Polymath arXiv:1402.0811v3, Definition 2.5,
  Theorem 2.9, Lemma 2.7 proof pp. 15--16 (source lines 1496--1589), crude
  divisor bounds (source lines 716--743), and Remark following that proof
  (source lines 1909--1915); Stadlmann's 2025 predecessor, coefficient
  definitions, Proposition 1, Lemma 19 and its Harman/Buchstab uses.
- **Claim proved at mathematical level:** Theorem 2.9 does imply a sharp
  `[x,2x]` estimate if its SW factor has the SW property uniformly after
  restriction to every multiplicative subinterval used by a partition with
  ratio `Theta=1+log(x)^(-D)`.  Interior boxes have no output cutoff;
  boundary boxes lie in collars of total length `O(x log(x)^(-D))` and are
  controlled by the divisor-function progression estimate.  There are only
  `O(log(x)^(2D+2))` boxes, absorbed by asking Theorem 2.9 for a larger
  logarithmic saving.
- **Important limitation:** global SW does not imply this local property;
  the counterexample is an explicit witness.  Stadlmann's printed Harman
  class records only global SW.  The 2025/2026 Harman reductions invoke this
  overbroad class and omit the fine-box/local-SW verification for every
  concrete atom.
- **Current best theorem:** a repaired, source-backed
  `LocallySiegelWalfiszSharpBV` derived from Polymath 2.9 plus its stated
  divisor progression bound.  It is sufficient only after every concrete
  Type-II atom has been shown to meet the local hypothesis.
- **Failed approaches so far:** direct truncation and prefix subtraction
  fail for lack of local control; ordinary dyadic support alignment leaves
  a macroscopic boundary; an arbitrary sharp theorem is refuted.
- **Files changed:** this checkpoint log only.
- **Next action:** finish the concrete coefficient trace and primary-source
  search, then freeze the weakest missing atom-level verification.

## Checkpoint 3 - primary sharp-conversion source and coefficient trace

- **Stage:** completed the primary-source adapter search and traced the
  printed class back through the 2025 Harman/Heath--Brown construction.
- **Sources inspected:** Fouvry--Radziwill arXiv:1811.08672 Definition 1,
  Corollary 1.1, Proposition 8.1 and pp. 25--26; Stadlmann 2025 Lemmas
  18--22; Polymath Section 3; Baker--Weingartner Lemma 14 and the
  Baker--Irving Type-II statement cited in that route.
- **Claim proved:** Fouvry--Radziwill give a rigorous smooth-output/Mellin
  adapter from a full-support bilinear estimate to `x<mn≤2x` when the SW
  factor is uniform on every dyadic interval. The proof has explicit collar,
  Mellin-height, twist-uniformity, and logarithmic-saving losses.
- **Coefficient result:** Stadlmann's printed Type-II class has no hidden
  generated list, positivity, or output-support condition. The intended
  Polymath atoms are more structured, but the 2025/2026 sources do not
  enumerate and prove local SW for every direct, sifted, coupled, and
  Baker--Weingartner term used in Proposition 2.
- **New source gap:** the Baker--Weingartner Lemma 14 route quantifies over
  arbitrary bounded test arrays, while the cited Type-II theorem assumes SW
  factors; the common exceptional-modulus bridge is not supplied.
- **Current best theorem:** `IntervalSWSharpBilinearBV`, derived from
  Polymath 2.9 using the Fouvry--Radziwill adapter. It is valid but does not
  apply until every concrete minorant Type-II term has a locally SW factor.
- **Failed routes:** positivity and well-factorability do not supply the
  missing output localization; ordinary dyadic partition, raw prefix
  subtraction, and raw Perron inversion still fail from global SW alone.
- **Files changed:** checkpoint log; exact verifier; resolution and author
  query drafted next.
- **Next action:** synchronize the analytic contract and gap ledgers, inspect
  the full diff, and rerun the unchanged Lean audits and complete build.

## Checkpoint 4 - contract synchronized and validation complete

- **Stage:** final statement freeze, artifact review, and unchanged-project
  validation.
- **Decision:** the arbitrary global-SW sharp theorem and Proposition 3's
  printed universal Type-II clause are refuted. The strongest proved adapter
  is `IntervalSWSharpBilinearBV`; the weakest remaining blocker is the
  complete generated-minorant membership/local-SW theorem, including the
  Baker--Weingartner route.
- **Files created:** `SHARP_OUTPUT_BV_RESOLUTION.md`,
  `AUTHOR_QUERY_SHARP_BV.md`, and `verify_sharp_counterexample.py`.
- **Files updated:** this checkpoint log, `ANALYTIC_CONTRACT.md`,
  `SOURCE_LEDGER.md`, and `GAP_REGISTER.md`.
- **Exact verifier:** completed successfully; complete-support discrepancy
  was exactly zero at every tested `T=60,120,240,480,960`, while the sharp
  ratio converged toward `-0.000504477452...`.
- **Lean statement audit:** `lake env lean H1236StatementAudit.lean` exited
  0. Axioms were `[propext]` for the explicit contract and
  `[propext, Classical.choice, Quot.sound]` for the tuple bridge and liminf
  equivalence.
- **Original baseline audit:** `lake env lean AxiomAudit.lean` exited 0 and
  reported `[propext, Classical.choice, Quot.sound]`.
- **Complete build:** `lake build` exited 0: `Build completed successfully
  (4434 jobs).` Existing informational messages in the concrete Maynard path
  were unchanged; there were no errors.
- **Diff/safety checks:** `git diff --check` exited 0 with no output. Git
  still reports the pre-existing untracked `Documentation/` tree and no
  changed Lean file. A trailing-whitespace scan over every 3F-touched file
  was empty. Because there is no changed Lean file, the changed-Lean
  `sorry`/`admit`/new-axiom scan has an empty target set.
- **Gate:** NO-GO for `AnalyticInput.lean`. The 236 result remains
  manuscript-conditional.

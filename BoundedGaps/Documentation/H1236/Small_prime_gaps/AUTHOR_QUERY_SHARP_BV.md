# Author query: the Type-II class and the sharp output interval

Proposition 3 of arXiv:2608.31126v1 quantifies over every Type-II
`f=alpha*beta` in Definition 9. That definition assumes fixed-multiple
support, divisor/polylog bounds, `MN≈x`, the Type-II exponent range, and
global Siegel--Walfisz for both factors. Definition 7 and Proposition 3 then
estimate the sharp restriction `f(n;x)1_[x,2x](n)`.

These printed hypotheses do not imply the conclusion. For `x=T^2`, bounded
balanced block sequences `alpha=t chi_3`, `beta=s chi_3` are both globally
Siegel--Walfisz, and the complete-support discrepancy at modulus 3 is zero,
but

```text
Delta((alpha*beta)1_[x,2x];1(3))
  = -c x + O(sqrt x),  c>0.
```

The example can also be summed over squarefree `q=3pr` in genuine nonzero
`Q*` cells to give `Omega(x)`. Polymath Theorem 2.9 is full-support; its
Section 3 application removes the sharp cutoff only after localizing the
specific Heath--Brown atoms. Fouvry--Radziwill, arXiv:1811.08672,
pp. 25--26, obtain a generic sharp adapter under a stronger SW definition
uniform on every dyadic interval.

**Exact question.** Was Proposition 3 intended to quantify only over the
finite/generated Buchstab--Heath--Brown terms actually occurring in the
proof of Proposition 2? If so, please specify that class and the proof that
one factor of every Type-II grouping is uniformly Siegel--Walfisz after all
short multiplicative interval restrictions (or uniformly after the Mellin
twists needed to impose `x≤mn≤2x`). Please include the direct sifted terms
and explain how the arbitrary test sequences in Baker--Weingartner Lemma 14,
invoked in the 2025 predecessor's Lemma 19, acquire a common uniform
distribution estimate.

Lean requires this choice because the universal printed class is refuted,
whereas a generated local-SW class has different data, quantifiers, and a
nontrivial membership theorem. This is not a request to assume an arbitrary
sharp-output BV theorem; it asks which restricted theorem the manuscript's
actual minorant proof establishes.

#!/usr/bin/env python3
"""Exact finite-sum check for the Milestone 3F modulo-3 counterexample.

This is evidence for, not a substitute for, the proof in
SHARP_OUTPUT_BV_RESOLUTION.md.  Every discrepancy is computed as a Fraction.
"""

from fractions import Fraction
from math import gcd, log


def chi3(n: int) -> int:
    residue = n % 3
    return 0 if residue == 0 else (1 if residue == 1 else -1)


def t_block(T: int, m: int) -> int:
    if T <= m < T + T // 20:
        return -1
    if T + T // 20 <= m <= T + T // 10:
        return 1
    return 0


def s_block(T: int, n: int) -> int:
    if T // 2 <= n < T:
        return -1
    if T <= n <= 3 * T // 2:
        return 1
    return 0


def discrepancy(T: int, sharp: bool) -> Fraction:
    modulus = 3
    residue_sum = 0
    coprime_sum = 0
    lower = T * T
    upper = 2 * lower
    for m in range(T, T + T // 10 + 1):
        alpha = t_block(T, m) * chi3(m)
        if alpha == 0:
            continue
        for n in range(T // 2, 3 * T // 2 + 1):
            beta = s_block(T, n) * chi3(n)
            if beta == 0:
                continue
            product = m * n
            if sharp and not (lower <= product <= upper):
                continue
            weight = alpha * beta
            if product % modulus == 1:
                residue_sum += weight
            if gcd(product, modulus) == 1:
                coprime_sum += weight
    return Fraction(residue_sum) - Fraction(coprime_sum, 2)


def main() -> None:
    h = Fraction(1, 10)
    c_h = 2.0 * log(1.0 + float(h) / 2.0) - log(1.0 + float(h))
    predicted = -2.0 * c_h / 9.0
    print(f"predicted limiting sharp discrepancy/x = {predicted:.12f}")
    for T in (60, 120, 240, 480, 960):
        full = discrepancy(T, sharp=False)
        sharp = discrepancy(T, sharp=True)
        ratio = float(sharp / (T * T))
        print(
            f"T={T:4d} full={full!s:>5s} sharp={sharp!s:>8s} "
            f"sharp/x={ratio:.12f}"
        )


if __name__ == "__main__":
    main()

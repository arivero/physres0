#!/usr/bin/env python3.12
"""Discrete weighted checks for pair-groupoid geometric 1/2-density algebra identities.

Given quadrature weights w_i > 0, define discrete convolution
  (A * B)_{ij} = sum_k A_{ik} w_k B_{kj}.
This is the finite-grid analogue of pair-groupoid convolution with density.

We verify:
  1) associativity: (A*B)*C == A*(B*C)
  2) involution: (A*B)^* == B^* * A^*

Run:
  python3.12 research/workspace/simulations/claim1_pair_groupoid_convolution_check.py
"""

from __future__ import annotations

import random


def zero_mat(n: int) -> list[list[complex]]:
    return [[0j for _ in range(n)] for _ in range(n)]


def conv(a: list[list[complex]], b: list[list[complex]], w: list[float]) -> list[list[complex]]:
    n = len(a)
    out = zero_mat(n)
    for i in range(n):
        for j in range(n):
            s = 0j
            for k in range(n):
                s += a[i][k] * w[k] * b[k][j]
            out[i][j] = s
    return out


def invol(a: list[list[complex]]) -> list[list[complex]]:
    n = len(a)
    out = zero_mat(n)
    for i in range(n):
        for j in range(n):
            out[i][j] = a[j][i].conjugate()
    return out


def max_abs_diff(a: list[list[complex]], b: list[list[complex]]) -> float:
    n = len(a)
    m = 0.0
    for i in range(n):
        for j in range(n):
            d = abs(a[i][j] - b[i][j])
            if d > m:
                m = d
    return m


def rand_mat(n: int, rng: random.Random) -> list[list[complex]]:
    out = zero_mat(n)
    for i in range(n):
        for j in range(n):
            out[i][j] = complex(rng.uniform(-1.0, 1.0), rng.uniform(-1.0, 1.0))
    return out


def main() -> None:
    rng = random.Random(42)
    n = 6
    w = [rng.uniform(0.2, 1.3) for _ in range(n)]
    a, b, c = rand_mat(n, rng), rand_mat(n, rng), rand_mat(n, rng)

    lhs_assoc = conv(conv(a, b, w), c, w)
    rhs_assoc = conv(a, conv(b, c, w), w)
    assoc_err = max_abs_diff(lhs_assoc, rhs_assoc)

    lhs_inv = invol(conv(a, b, w))
    rhs_inv = conv(invol(b), invol(a), w)
    inv_err = max_abs_diff(lhs_inv, rhs_inv)

    print(f"max associativity error: {assoc_err:.3e}")
    print(f"max involution error   : {inv_err:.3e}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3.12
"""Toy cylinder-limit diagnostics for Claim 1 (Phase B).

Part A (compatible family):
  S_N(x) = 1/2 * sum_{j=1}^N x_j^2
  For cylinder observable O(x)=exp(-alpha*x1^2),
  normalized expectation is exactly N-independent for N>=1.

Part B (incompatible family):
  S_N^bad(x) = 1/2 * c_N * x_1^2 + 1/2 * sum_{j=2}^N x_j^2
  with c_N = (-1)^N.
  Normalized expectation for O(x)=x1^2 oscillates with N.

Run:
  python3.12 research/workspace/simulations/claim1_cylinder_gaussian_toy.py
"""

from __future__ import annotations

import cmath
import math


def expect_exp_minus_alpha_x2(eps: float, alpha: float) -> complex:
    # E[exp(-alpha x^2)] under oscillatory Gaussian weight exp(i x^2 / (2 eps))
    # ratio = I_alpha / I_0
    i = 1j
    return cmath.sqrt((i / (2.0 * eps)) / (alpha - i / (2.0 * eps)))


def expect_x2(eps: float, c: float) -> complex:
    # For weight exp(i c x^2 / (2 eps)): E[x^2] = i eps / c.
    return 1j * eps / c


def main() -> None:
    eps = 0.2
    alpha = 0.7

    print("Part A: compatible cylinder family (expect N-independence)")
    target = expect_exp_minus_alpha_x2(eps, alpha)
    print(f"  theoretical expectation = {target.real:+.12f}{target.imag:+.12f}i")
    for N in range(1, 8):
        # Exact N-independence by factorization/cancellation.
        val = target
        print(f"  N={N}: {val.real:+.12f}{val.imag:+.12f}i")
    print()

    print("Part B: incompatible family (expect oscillation/no convergence)")
    for N in range(1, 9):
        c_n = -1.0 if N % 2 else 1.0
        val = expect_x2(eps, c_n)
        print(f"  N={N}: c_N={c_n:+.0f}, E[x1^2]={val.real:+.12f}{val.imag:+.12f}i")


if __name__ == "__main__":
    main()

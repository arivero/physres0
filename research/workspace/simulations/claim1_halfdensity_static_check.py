#!/usr/bin/env python3.12
"""Closed-form sanity check for Claim 1 static probability-amplitude scaling.

Model choice:
  f(x) = x^2 / 2, O(x) = exp(-x^2 / 2), m = 1.

Then
  A_eps = eps^(-1/2) * integral exp(i f(x)/eps) O(x) dx
        = eps^(-1/2) * sqrt(2*pi / (1 - i/eps)),
so
  |A_eps|^2 = 2*pi / sqrt(1 + eps^2) -> 2*pi as eps -> 0+.

Run:
  python3.12 research/workspace/simulations/claim1_halfdensity_static_check.py
"""

from __future__ import annotations

import cmath
import math


def a_eps(eps: float) -> complex:
    return eps ** (-0.5) * cmath.sqrt((2.0 * math.pi) / (1.0 - 1j / eps))


def main() -> None:
    target = 2.0 * math.pi
    print(f"target limit 2pi = {target:.12f}")
    print()
    for eps in [1.0, 0.5, 0.2, 0.1, 0.05, 0.01, 0.005]:
        val = abs(a_eps(eps)) ** 2
        err = abs(val - target)
        print(f"eps={eps:7.4f}  |A_eps|^2={val:.12f}  abs_err={err:.3e}")


if __name__ == "__main__":
    main()

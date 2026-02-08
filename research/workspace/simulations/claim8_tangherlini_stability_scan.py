#!/usr/bin/env python3.12
"""Stability scan for Tangherlini circular timelike orbits across dimensions.

Run:
  python3.12 research/workspace/simulations/claim8_tangherlini_stability_scan.py
"""

from __future__ import annotations

import math


def circular_l2(D: int, mu: float, r: float) -> float | None:
    q = D - 3.0
    denom = 2.0 * (r**q) - (q + 2.0) * mu
    if denom <= 0.0:
        return None
    return q * mu * r * r / denom


def stability_indicator(D: int, l2: float, r: float) -> float:
    q = D - 3.0
    # Sign of V_eff'' at circular orbit (up to positive prefactor mu*q*r^{-q-4}).
    return (2.0 - q) * r * r - (q + 2.0) * l2


def report(D: int, mu: float, r: float) -> None:
    l2 = circular_l2(D, mu, r)
    print(f"D={D}, r={r:.6f}")
    if l2 is None:
        print("  no circular orbit at this radius (existence denominator <= 0)")
        print()
        return
    ind = stability_indicator(D, l2, r)
    verdict = "stable" if ind > 0.0 else "unstable"
    print(f"  l^2={l2:.6f}, stability_indicator={ind:.6f} -> {verdict}")
    print()


def main() -> None:
    mu = 2.0

    # D=4 reference: both unstable and stable circular examples.
    report(D=4, mu=mu, r=5.0)   # unstable (below r=6 for M=1, mu=2)
    report(D=4, mu=mu, r=8.0)   # stable

    # D>=5: should always be unstable for existing circular radii.
    for D in [5, 6, 7, 8]:
        q = D - 3.0
        r_min = (((q + 2.0) * mu) / 2.0) ** (1.0 / q)
        report(D=D, mu=mu, r=1.5 * r_min)
        report(D=D, mu=mu, r=3.0 * r_min)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3.12
"""Far-zone stability sign scan for high-D asymptotic gravity (Claim 8 extension).

Run:
  python3.12 research/workspace/simulations/claim8_asymptotic_stability_sign.py
"""

from __future__ import annotations


def classify(D: int) -> str:
    s = 5 - D
    if s > 0:
        return "stable"
    if s == 0:
        return "marginal"
    return "unstable"


def main() -> None:
    for D in [4, 5, 6, 7, 8]:
        s = 5 - D
        print(f"D={D}: sign factor (5-D)={s:+d} -> far-zone circular {classify(D)}")


if __name__ == "__main__":
    main()

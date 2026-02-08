#!/usr/bin/env python3.12
"""Global-time allowed-set topology diagnostics for Claim 4 (n=3 SR).

Run:
  python3.12 research/workspace/simulations/claim4_global_time_shell_scan.py
"""

from __future__ import annotations

import math
from dataclasses import dataclass


@dataclass
class Case:
    name: str
    E: float
    L: float
    m: float = 1.0
    c: float = 1.0
    K: float = 1.0


def coeffs(case: Case) -> tuple[float, float, float]:
    a2 = (case.K * case.K) / (4.0 * case.c * case.c)
    a1 = (case.E * case.K) / (case.c * case.c) - (case.L * case.L)
    a0 = (case.E * case.E - (case.m * case.c * case.c) ** 2) / (case.c * case.c)
    return a2, a1, a0


def positive_roots_y(a2: float, a1: float, a0: float) -> list[float]:
    eps = 1e-12
    disc = a1 * a1 - 4.0 * a2 * a0
    if disc < -eps:
        return []
    disc = max(0.0, disc)
    s = math.sqrt(disc)
    y1 = (-a1 - s) / (2.0 * a2)
    y2 = (-a1 + s) / (2.0 * a2)
    roots = sorted([y for y in [y1, y2] if y >= 0.0])
    ded: list[float] = []
    for y in roots:
        if not ded or abs(y - ded[-1]) > 1e-9:
            ded.append(y)
    return ded


def classify(case: Case) -> None:
    a2, a1, a0 = coeffs(case)
    ys = positive_roots_y(a2, a1, a0)
    print(case.name)
    print(f"  coeffs: a2={a2:+.6f}, a1={a1:+.6f}, a0={a0:+.6f}, roots_y={ys}")

    if len(ys) == 0:
        lab = "all-y-allowed or one-side allowed; no finite bounded shell"
    elif len(ys) == 1:
        lab = "single-threshold branch split; no periodic shell"
    else:
        y_lo, y_hi = ys
        r_hi = (1.0 / math.sqrt(y_lo)) if y_lo > 0.0 else float("inf")
        r_lo = 1.0 / math.sqrt(y_hi)
        lab = (
            "two-channel topology: escape branch (r >= %.4f) and plunge branch (r <= %.4f); "
            "forbidden gap in between" % (r_hi, r_lo)
        )
    print(f"  classification: {lab}")
    print()


def main() -> None:
    cases = [
        Case("sub-rest energy, moderate L", E=0.9, L=0.8),
        Case("super-rest energy, moderate L", E=1.2, L=0.8),
        Case("super-rest energy, large L", E=1.2, L=2.0),
        Case("near-threshold tuning", E=1.0, L=1.0),
    ]
    for c in cases:
        classify(c)


if __name__ == "__main__":
    main()

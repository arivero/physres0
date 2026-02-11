#!/usr/bin/env python3.12
"""Threshold scan for Claim 6 Phase E (null Schwarzschild lane).

Run:
  python3.12 research/workspace/simulations/claim6_null_schwarzschild_threshold_scan.py
"""

from __future__ import annotations

import math

import numpy as np


def exterior_roots(b: float, horizon_eps: float = 1e-8) -> list[float]:
    coeff = [1.0, 0.0, -(b * b), 2.0 * b * b]
    roots = np.roots(coeff)
    real_roots = []
    for z in roots:
        if abs(z.imag) < 1e-9:
            r = float(z.real)
            if r > 2.0 + horizon_eps:
                real_roots.append(r)
    real_roots.sort()
    ded: list[float] = []
    for r in real_roots:
        if not ded or abs(r - ded[-1]) > 1e-7:
            ded.append(r)
    return ded


def classify(b: float, bcrit: float) -> str:
    tol = 2e-6
    roots = exterior_roots(b)
    if b < bcrit - tol:
        return "capture (no exterior turning point)" if len(roots) == 0 else "unexpected"
    if abs(b - bcrit) <= tol:
        has_three = any(abs(r - 3.0) < 2e-6 for r in roots)
        return "critical separatrix" if has_three else "unexpected"
    return "scatter (exterior turning point exists)" if len(roots) >= 1 else "unexpected"


def main() -> None:
    bcrit = 3.0 * math.sqrt(3.0)
    print(f"bcrit={bcrit:.12f}")

    cases = [
        (4.8, "capture (no exterior turning point)"),
        (bcrit, "critical separatrix"),
        (5.8, "scatter (exterior turning point exists)"),
        (8.0, "scatter (exterior turning point exists)"),
    ]

    all_ok = True
    for b, expected in cases:
        roots = exterior_roots(b)
        label = classify(b, bcrit)
        ok = label == expected
        all_ok = all_ok and ok
        print(
            f"b={b:.12f}: roots_outside_horizon={roots}, "
            f"label={label}, expected={expected}, ok={ok}"
        )

    print(f"all_checks_pass={all_ok}")


if __name__ == "__main__":
    main()

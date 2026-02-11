#!/usr/bin/env python3.12
"""Consistency check for Claim 3 Phase Y.

Checks equality between:
  1) roots of Q(u)=A+2Bu-alpha^2 u^2,
  2) u_c +/- e from phase representation.

Run:
  python3.12 research/workspace/simulations/claim3_root_rotation_consistency_check.py
"""

from __future__ import annotations

import math
from dataclasses import dataclass


EPS = 1e-10


@dataclass
class Case:
    name: str
    E: float
    L: float
    m: float = 1.0
    c: float = 1.0
    K: float = 1.0


def invariants(case: Case) -> tuple[float, float, float]:
    alpha2 = 1.0 - (case.K * case.K) / (case.L * case.L * case.c * case.c)
    A = (case.E * case.E - (case.m * case.c * case.c) ** 2) / (case.L * case.L * case.c * case.c)
    B = case.K * case.E / (case.L * case.L * case.c * case.c)
    return alpha2, A, B


def roots_from_quadratic(alpha2: float, A: float, B: float) -> tuple[float, float] | None:
    if alpha2 <= EPS:
        return None
    disc = B * B + alpha2 * A
    if disc < -EPS:
        return None
    disc = max(0.0, disc)
    s = math.sqrt(disc)
    u1 = (B - s) / alpha2
    u2 = (B + s) / alpha2
    return (min(u1, u2), max(u1, u2))


def roots_from_phase(alpha2: float, A: float, B: float) -> tuple[float, float] | None:
    if alpha2 <= EPS:
        return None
    uc = B / alpha2
    e2 = (B * B + alpha2 * A) / (alpha2 * alpha2)
    if e2 < -EPS:
        return None
    e2 = max(0.0, e2)
    e = math.sqrt(e2)
    u1 = uc - e
    u2 = uc + e
    return (min(u1, u2), max(u1, u2))


def classify_A(A: float) -> str:
    if A < -1e-9:
        return "A<0 bounded-shell"
    if A > 1e-9:
        return "A>0 one-positive-root scattering"
    return "A=0 threshold"


def run_case(case: Case) -> tuple[bool, str]:
    alpha2, A, B = invariants(case)
    rq = roots_from_quadratic(alpha2, A, B)
    rp = roots_from_phase(alpha2, A, B)

    if rq is None or rp is None:
        return False, f"{case.name}: invalid oscillatory branch (alpha2={alpha2:+.6e})"

    err = max(abs(rq[0] - rp[0]), abs(rq[1] - rp[1]))
    positive_roots = sum(1 for u in rq if u > 1e-9)

    if A < -1e-9:
        expected_positive = 2
    elif A > 1e-9:
        expected_positive = 1
    else:
        expected_positive = 1

    ok = (err < 1e-10) and (positive_roots == expected_positive)

    detail = (
        f"{case.name}: alpha2={alpha2:+.6f}, A={A:+.6f}, B={B:+.6f}, "
        f"roots_quadratic={rq}, roots_phase={rp}, max_err={err:.3e}, "
        f"positive_roots={positive_roots}, expected_positive={expected_positive}, "
        f"label={classify_A(A)}, ok={ok}"
    )
    return ok, detail


def main() -> None:
    cases = [
        Case(name="E<mc^2 branch", E=0.8, L=1.4),
        Case(name="E=mc^2 threshold", E=1.0, L=1.4),
        Case(name="E>mc^2 scattering", E=1.2, L=1.4),
        Case(name="high-energy scattering", E=1.6, L=2.0),
    ]

    all_ok = True
    for case in cases:
        ok, detail = run_case(case)
        print(detail)
        all_ok = all_ok and ok

    print(f"all_checks_pass={all_ok}")


if __name__ == "__main__":
    main()

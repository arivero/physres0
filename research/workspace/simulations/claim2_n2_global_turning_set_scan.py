#!/usr/bin/env python3.12
"""Global turning-set diagnostics for Claim 2 Phase E (n=2 Coulomb lane).

Run:
  python3.12 research/workspace/simulations/claim2_n2_global_turning_set_scan.py
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
    expected_center_access: bool = False
    expected_components: int = 0


def coeffs(case: Case) -> tuple[float, float, float]:
    a = (case.K * case.K) / (case.c * case.c) - case.L * case.L
    b = (2.0 * case.E * case.K) / (case.c * case.c)
    d = (case.E * case.E - (case.m * case.c * case.c) ** 2) / (case.c * case.c)
    return a, b, d


def p_u(u: float, a: float, b: float, d: float) -> float:
    return a * u * u + b * u + d


def positive_roots(a: float, b: float, d: float) -> list[float]:
    roots: list[float] = []
    if abs(a) <= EPS:
        if abs(b) > EPS:
            u = -d / b
            if u > 0.0:
                roots.append(u)
        return roots

    disc = b * b - 4.0 * a * d
    if disc < -EPS:
        return roots
    disc = max(0.0, disc)
    s = math.sqrt(disc)
    u1 = (-b - s) / (2.0 * a)
    u2 = (-b + s) / (2.0 * a)
    for u in [u1, u2]:
        if u > 0.0:
            roots.append(u)
    roots.sort()
    ded: list[float] = []
    for u in roots:
        if not ded or abs(u - ded[-1]) > 1e-8:
            ded.append(u)
    return ded


def component_count(a: float, b: float, d: float, umax: float) -> int:
    n = 24000
    count = 0
    in_component = False
    for i in range(n + 1):
        u = umax * i / n
        val = p_u(u, a, b, d)
        allowed = val >= -1e-9
        if allowed and not in_component:
            count += 1
            in_component = True
        if not allowed and in_component:
            in_component = False
    return count


def predicted_center_access(a: float, b: float, d: float) -> bool:
    if a > EPS:
        return True
    if a < -EPS:
        return False
    if b > EPS:
        return True
    if b < -EPS:
        return False
    return d > 0.0


def run_case(case: Case) -> tuple[bool, str]:
    a, b, d = coeffs(case)
    roots = positive_roots(a, b, d)
    umax = max(40.0, 8.0 + 10.0 * (roots[-1] if roots else 0.0))

    center_pred = predicted_center_access(a, b, d)
    center_obs = p_u(umax, a, b, d) > 0.0
    comps = component_count(a, b, d, umax)

    ok = (
        (center_pred == center_obs)
        and (center_pred == case.expected_center_access)
        and (comps == case.expected_components)
    )

    detail = (
        f"{case.name}: a={a:+.6f}, b={b:+.6f}, d={d:+.6f}, "
        f"positive_roots={roots}, center_pred={center_pred}, "
        f"center_obs={center_obs}, components={comps}, "
        f"expected_center={case.expected_center_access}, "
        f"expected_components={case.expected_components}, ok={ok}"
    )
    return ok, detail


def main() -> None:
    cases = [
        Case(
            name="a<0, one positive root (scattering band)",
            E=1.2,
            L=1.2,
            expected_center_access=False,
            expected_components=1,
        ),
        Case(
            name="a<0, two positive roots (bounded shell)",
            E=0.8,
            L=1.2,
            expected_center_access=False,
            expected_components=1,
        ),
        Case(
            name="a=0, E>0 (critical capture-open)",
            E=1.2,
            L=1.0,
            expected_center_access=True,
            expected_components=1,
        ),
        Case(
            name="a=0, E<0 (critical center-excluded)",
            E=-1.2,
            L=1.0,
            expected_center_access=False,
            expected_components=1,
        ),
        Case(
            name="a>0, no positive roots (all-u allowed)",
            E=1.2,
            L=0.8,
            expected_center_access=True,
            expected_components=1,
        ),
        Case(
            name="a>0, two positive roots (split low/high channels)",
            E=-1.2,
            L=0.8,
            expected_center_access=True,
            expected_components=2,
        ),
    ]

    all_ok = True
    for case in cases:
        ok, detail = run_case(case)
        print(detail)
        all_ok = all_ok and ok

    print(f"all_checks_pass={all_ok}")


if __name__ == "__main__":
    main()

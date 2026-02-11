#!/usr/bin/env python3.12
"""Asymptotic-time diagnostics for Claim 4 Phase E (n=3 SR).

Checks:
  1) dt/dr -> 1/c as r -> 0 on center-access branches.
  2) dr/dt -> v_inf as r -> infinity for E>mc^2 outgoing branches.

Run:
  python3.12 research/workspace/simulations/claim4_n3_time_asymptotics_check.py
"""

from __future__ import annotations

import math
from dataclasses import dataclass


@dataclass
class Case:
    name: str
    E: float
    L: float
    K: float
    m: float = 1.0
    c: float = 1.0


def p_r_sq(r: float, case: Case) -> float:
    term4 = (case.K * case.K) / (4.0 * case.c * case.c) / (r**4)
    term2 = ((case.E * case.K) / (case.c * case.c) - case.L * case.L) / (r * r)
    term0 = (case.E * case.E - (case.m * case.c * case.c) ** 2) / (case.c * case.c)
    return term4 + term2 + term0


def dt_dr(r: float, case: Case) -> float:
    prs = p_r_sq(r, case)
    if prs <= 0.0:
        raise ValueError("outside allowed region")
    pr = math.sqrt(prs)
    return (case.E + case.K / (2.0 * r * r)) / (case.c * case.c * pr)


def check_center_limit(case: Case) -> tuple[bool, str]:
    target = 1.0 / case.c
    radii = [1e-1, 5e-2, 2e-2, 1e-2, 5e-3]
    errs = []
    for r in radii:
        val = dt_dr(r, case)
        errs.append(abs(val - target))
    monotone = all(errs[i + 1] <= errs[i] + 1e-12 for i in range(len(errs) - 1))
    tight = errs[-1] < 3e-4
    ok = monotone and tight
    detail = (
        f"{case.name} center-limit: target=1/c={target:.10f}, "
        f"errors={['%.3e' % e for e in errs]}, monotone={monotone}, tight={tight}, ok={ok}"
    )
    return ok, detail


def check_escape_limit(case: Case) -> tuple[bool, str]:
    if case.E <= case.m * case.c * case.c:
        return False, f"{case.name} escape-limit skipped (E<=mc^2)"

    p_inf = math.sqrt(case.E * case.E - (case.m * case.c * case.c) ** 2) / case.c
    v_inf = case.c * case.c * p_inf / case.E

    radii = [20.0, 40.0, 80.0, 160.0]
    errs = []
    for r in radii:
        val = 1.0 / dt_dr(r, case)
        errs.append(abs(val - v_inf))
    monotone = all(errs[i + 1] <= errs[i] + 1e-12 for i in range(len(errs) - 1))
    tight = errs[-1] < 5e-5
    ok = monotone and tight
    detail = (
        f"{case.name} escape-limit: target=v_inf={v_inf:.10f}, "
        f"errors={['%.3e' % e for e in errs]}, monotone={monotone}, tight={tight}, ok={ok}"
    )
    return ok, detail


def main() -> None:
    cases = [
        Case(name="case-A", E=1.3, L=0.8, K=1.0),
        Case(name="case-B", E=1.6, L=2.0, K=1.2),
    ]

    all_ok = True
    for case in cases:
        ok_c, msg_c = check_center_limit(case)
        ok_e, msg_e = check_escape_limit(case)
        print(msg_c)
        print(msg_e)
        all_ok = all_ok and ok_c and ok_e

    print(f"all_checks_pass={all_ok}")


if __name__ == "__main__":
    main()

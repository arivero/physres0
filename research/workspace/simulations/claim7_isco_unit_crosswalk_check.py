#!/usr/bin/env python3.12
"""Unit crosswalk diagnostics for Claim 7 ISCO thresholds.

Run:
  python3.12 research/workspace/simulations/claim7_isco_unit_crosswalk_check.py
"""

from __future__ import annotations

import math
from dataclasses import dataclass


G = 6.67430e-11
c = 299792458.0


@dataclass
class Case:
    name: str
    M: float
    m: float


def isco_values(case: Case) -> tuple[float, float, float, float]:
    r_isco = 6.0 * G * case.M / (c * c)
    ell_isco = math.sqrt(12.0) * G * case.M / c
    L_isco = case.m * ell_isco
    E_ratio = math.sqrt(8.0 / 9.0)
    return r_isco, ell_isco, L_isco, E_ratio


def check_case(case: Case) -> tuple[bool, str]:
    r_isco, ell_isco, L_isco, E_ratio = isco_values(case)

    rhat = (c * c * r_isco) / (G * case.M)
    lhat = (c * ell_isco) / (G * case.M)
    ltot_hat = (c * L_isco) / (G * case.M * case.m)

    ok = (
        abs(rhat - 6.0) < 1e-12
        and abs(lhat - math.sqrt(12.0)) < 1e-12
        and abs(ltot_hat - math.sqrt(12.0)) < 1e-12
        and abs(E_ratio - math.sqrt(8.0 / 9.0)) < 1e-15
    )

    detail = (
        f"{case.name}: r_isco={r_isco:.6e} m, ell_isco={ell_isco:.6e} m^2/s, "
        f"L_isco={L_isco:.6e} kg m^2/s, rhat={rhat:.12f}, lhat={lhat:.12f}, "
        f"E_ratio={E_ratio:.12f}, ok={ok}"
    )
    return ok, detail


def main() -> None:
    cases = [
        Case(name="solar-mass source", M=1.98847e30, m=1.0),
        Case(name="ten-solar-mass source", M=1.98847e31, m=2.5),
        Case(name="supermassive source", M=4.3e6 * 1.98847e30, m=0.5),
    ]

    all_ok = True
    for case in cases:
        ok, detail = check_case(case)
        print(detail)
        all_ok = all_ok and ok

    print(f"all_checks_pass={all_ok}")


if __name__ == "__main__":
    main()

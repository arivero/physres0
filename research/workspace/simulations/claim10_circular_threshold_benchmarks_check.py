#!/usr/bin/env python3.12
"""Regression checks for Claim 10 circular-threshold benchmarks.

Run:
  python3.12 research/workspace/simulations/claim10_circular_threshold_benchmarks_check.py
"""

from __future__ import annotations

import math

import sympy as sp


def symbolic_checks() -> tuple[bool, str]:
    m, v, r, c = sp.symbols("m v r c", positive=True)
    gamma = 1 / sp.sqrt(1 - v**2 / c**2)

    # n=2: K = gamma m v^2 r, L = gamma m v r => K/L - v = 0
    K2 = gamma * m * v**2 * r
    L2 = gamma * m * v * r
    res2 = sp.simplify(K2 / L2 - v)

    # n=3: K = gamma m v^2 r^2, L = gamma m v r => L^2/(K m) - gamma = 0
    K3 = gamma * m * v**2 * r**2
    L3 = gamma * m * v * r
    res3 = sp.simplify((L3**2) / (K3 * m) - gamma)

    ok = (res2 == 0) and (res3 == 0)
    detail = f"symbolic_residuals: n2={res2}, n3={res3}, ok={ok}"
    return ok, detail


def numeric_checks() -> tuple[bool, str]:
    c = 1.0
    m = 1.7
    radii = [0.5, 1.0, 2.5]
    velocities = [0.1, 0.3, 0.6, 0.85]

    min_margin_n2 = float("inf")
    min_margin_n3 = float("inf")
    max_identity_err = 0.0

    for r in radii:
        for v in velocities:
            gamma = 1.0 / math.sqrt(1.0 - (v * v) / (c * c))

            # n=2 lane
            K2 = gamma * m * v * v * r
            L2 = gamma * m * v * r
            identity_err2 = abs(K2 / L2 - v)
            margin2 = L2 - K2 / c
            min_margin_n2 = min(min_margin_n2, margin2)

            # n=3 lane
            K3 = gamma * m * v * v * r * r
            L3 = gamma * m * v * r
            identity_err3 = abs((L3 * L3) / (K3 * m) - gamma)
            margin3 = L3 * L3 - K3 * m
            min_margin_n3 = min(min_margin_n3, margin3)

            max_identity_err = max(max_identity_err, identity_err2, identity_err3)

    # Endpoint probe for n=3 weak inequality saturation as v -> 0.
    v_small = 1e-6
    gamma_small = 1.0 / math.sqrt(1.0 - v_small * v_small)
    r_small = 1.0
    K3_small = gamma_small * m * v_small * v_small * r_small * r_small
    L3_small = gamma_small * m * v_small * r_small
    endpoint_gap = L3_small * L3_small - K3_small * m

    ok = (
        min_margin_n2 > 0.0
        and min_margin_n3 > 0.0
        and max_identity_err < 5e-13
        and endpoint_gap >= 0.0
    )

    detail = (
        f"numeric: min_margin_n2={min_margin_n2:.6e}, "
        f"min_margin_n3={min_margin_n3:.6e}, "
        f"max_identity_err={max_identity_err:.3e}, "
        f"endpoint_gap_v1e-6={endpoint_gap:.6e}, ok={ok}"
    )
    return ok, detail


def main() -> None:
    ok_sym, msg_sym = symbolic_checks()
    ok_num, msg_num = numeric_checks()
    print(msg_sym)
    print(msg_num)
    print(f"all_checks_pass={ok_sym and ok_num}")


if __name__ == "__main__":
    main()

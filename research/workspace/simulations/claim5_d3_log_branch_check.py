#!/usr/bin/env python3.12
"""Diagnostic check for Claim 5 Phase E (D=3 log-potential branch).

Run:
  python3.12 research/workspace/simulations/claim5_d3_log_branch_check.py
"""

from __future__ import annotations

import math


def potential_log(r: float, G3: float, M: float, r0: float) -> float:
    return -G3 * M * math.log(r / r0)


def force_exact(r: float, G3: float, m: float, M: float) -> float:
    return G3 * m * M / r


def force_fd(r: float, G3: float, m: float, M: float, r0: float, hfrac: float = 1e-6) -> float:
    h = hfrac * r
    vp = potential_log(r + h, G3, M, r0)
    vm = potential_log(r - h, G3, M, r0)
    dphi = (vp - vm) / (2.0 * h)
    return m * abs(dphi)


def main() -> None:
    G3 = 1.7
    M = 2.3
    m = 0.9
    r0 = 1.0

    radii = [0.2, 0.35, 0.7, 1.3, 2.7, 5.0, 9.0]
    rel_errs = []

    for r in radii:
        f_ex = force_exact(r, G3, m, M)
        f_num = force_fd(r, G3, m, M, r0)
        rel = abs(f_num - f_ex) / f_ex
        rel_errs.append(rel)
        print(
            f"r={r:>4.2f}: F_exact={f_ex:.10f}, F_fd={f_num:.10f}, rel_err={rel:.3e}"
        )

    max_rel = max(rel_errs)
    all_ok = max_rel < 5e-9
    print(f"max_relative_error={max_rel:.3e}")
    print(f"all_checks_pass={all_ok}")


if __name__ == "__main__":
    main()

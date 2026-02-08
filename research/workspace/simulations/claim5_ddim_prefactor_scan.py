#!/usr/bin/env python3.12
"""Prefactor sanity scan for Claim 5 D-dimensional GR matching.

Run:
  python3.12 research/workspace/simulations/claim5_ddim_prefactor_scan.py
"""

from __future__ import annotations

import math


def omega(d: int) -> float:
    return 2.0 * math.pi ** ((d + 1.0) / 2.0) / math.gamma((d + 1.0) / 2.0)


def prefactor(D: int) -> float:
    return 8.0 * math.pi * (D - 3.0) / ((D - 2.0) * omega(D - 2))


def main() -> None:
    for D in [4, 5, 6, 7, 8]:
        om = omega(D - 2)
        pf = prefactor(D)
        print(f"D={D}: Omega_(D-2)={om:.12f}, prefactor={pf:.12f}")
    print()
    print("D=4 check (expect 1):")
    print(f"  prefactor(4)={prefactor(4):.12f}")


if __name__ == "__main__":
    main()

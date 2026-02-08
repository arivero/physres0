#!/usr/bin/env python3.12
"""Numerical sanity scan for the Claim 2 center-access trichotomy.

Run:
  python3.12 research/workspace/simulations/claim2_trichotomy_scan.py
"""

from __future__ import annotations

from dataclasses import dataclass


def potential(r: float, K: float, n: float) -> float:
    return -K / (n - 1.0) * r ** (1.0 - n)


def pr2(r: float, *, E: float, L: float, m: float, c: float, K: float, n: float) -> float:
    # For n=2, use the exact expanded form to avoid catastrophic cancellation
    # in the critical branch L=K/c at very small r.
    if abs(n - 2.0) < 1e-14:
        a = (K * K) / (c * c) - (L * L)
        b = (2.0 * E * K) / (c * c)
        d = (E * E - (m * c * c) ** 2) / (c * c)
        return a / (r * r) + b / r + d
    v = potential(r, K, n)
    return ((E - v) ** 2 - (m * c * c) ** 2) / (c * c) - (L * L) / (r * r)


def sign(x: float) -> str:
    if x > 0:
        return "+"
    if x < 0:
        return "-"
    return "0"


@dataclass
class Case:
    name: str
    E: float
    L: float
    m: float
    c: float
    K: float
    n: float


def run_case(case: Case) -> None:
    rs = [10.0 ** (-k) for k in range(1, 9)]
    vals = [pr2(r, E=case.E, L=case.L, m=case.m, c=case.c, K=case.K, n=case.n) for r in rs]
    signs = "".join(sign(v) for v in vals)
    print(f"{case.name}")
    print(f"  params: n={case.n}, K={case.K}, m={case.m}, c={case.c}, E={case.E}, L={case.L}")
    print(f"  signs on r=1e-1..1e-8: {signs}")
    print(f"  last value p_r^2(1e-8)={vals[-1]:.6e}")
    print()


def main() -> None:
    cases = [
        Case("1<n<2, L!=0 (expect center-excluded)", E=2.0, L=2.0, m=1.0, c=1.0, K=1.0, n=1.5),
        Case("1<n<2, L=0 (expect center-allowed)", E=2.0, L=0.0, m=1.0, c=1.0, K=1.0, n=1.5),
        Case("n=2, L>K/c (expect center-excluded)", E=2.0, L=1.2, m=1.0, c=1.0, K=1.0, n=2.0),
        Case("n=2, L<K/c (expect center-allowed)", E=2.0, L=0.8, m=1.0, c=1.0, K=1.0, n=2.0),
        Case("n=2, L=K/c, E>0 (critical branch: expect center-allowed)", E=2.0, L=1.0, m=1.0, c=1.0, K=1.0, n=2.0),
        Case("n=2, L=K/c, E<0 (critical branch: expect center-excluded)", E=-2.0, L=1.0, m=1.0, c=1.0, K=1.0, n=2.0),
        Case("n=2, L=K/c, E=0 (critical branch: expect no allowed radii)", E=0.0, L=1.0, m=1.0, c=1.0, K=1.0, n=2.0),
        Case("n>2, finite L (expect center-allowed)", E=2.0, L=5.0, m=1.0, c=1.0, K=1.0, n=3.0),
    ]
    for case in cases:
        run_case(case)


if __name__ == "__main__":
    main()

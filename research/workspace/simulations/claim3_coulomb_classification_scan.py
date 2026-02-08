#!/usr/bin/env python3.12
"""Numerical diagnostics for Claim 3 Coulomb phase classification.

Run:
  python3.12 research/workspace/simulations/claim3_coulomb_classification_scan.py
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


def invariants(case: Case) -> tuple[float, float, float]:
    alpha2 = 1.0 - (case.K * case.K) / (case.L * case.L * case.c * case.c)
    a = (case.E * case.E - (case.m * case.c * case.c) ** 2) / (case.L * case.L * case.c * case.c)
    b = case.K * case.E / (case.c * case.c * case.L * case.L)
    return alpha2, a, b


def classify(case: Case) -> None:
    alpha2, a, b = invariants(case)
    print(case.name)
    print(f"  params: E={case.E:.6f}, L={case.L:.6f}, m={case.m:.6f}, c={case.c:.6f}, K={case.K:.6f}")
    print(f"  alpha^2={alpha2:.6f}, A={a:.6f}, B={b:.6f}")

    if alpha2 > 1e-12:
        alpha = math.sqrt(alpha2)
        u_center = b / alpha2
        disc = b * b + alpha2 * a
        if disc < 0.0:
            print("  classification: no real oscillatory branch (disc < 0)")
            print()
            return
        e = math.sqrt(disc) / alpha2
        u_min = u_center - e
        u_max = u_center + e
        if case.E > 0.0 and a < 0.0 and u_min > 0.0:
            regime = "L>K/c, bound rosette branch"
        elif case.E > 0.0 and abs(a) <= 1e-12:
            regime = "L>K/c, threshold branch (u_min ~ 0)"
        elif case.E > 0.0 and a > 0.0:
            regime = "L>K/c, scattering branch"
        else:
            regime = "L>K/c, nonstandard sign-E branch"
        print(f"  rotation number Theta={alpha:.6f}")
        print(f"  u_center={u_center:.6f}, e={e:.6f}, u_min={u_min:.6f}, u_max={u_max:.6f}")
        print(f"  classification: {regime}")
        print()
        return

    if abs(alpha2) <= 1e-12:
        slope2 = case.E / case.K
        if case.E > 0.0:
            regime = "L=K/c, critical marginal plunge branch"
        elif case.E < 0.0:
            regime = "L=K/c, critical non-plunge branch"
        else:
            regime = "L=K/c, degenerate constant-acceleration-zero branch"
        print(f"  u'' = E/K = {slope2:.6f}")
        print(f"  classification: {regime}")
        print()
        return

    lam = math.sqrt(-alpha2)
    u_particular = -b / (lam * lam)
    if case.E > 0.0:
        regime = "L<K/c, hyperbolic spiral/plunge regime"
    else:
        regime = "L<K/c, hyperbolic non-periodic regime"
    print(f"  lambda={lam:.6f}, particular u_p={u_particular:.6f}")
    print(f"  classification: {regime}")
    print()


def main() -> None:
    cases = [
        Case("L>K/c with E<mc^2 (expect bound)", E=0.8, L=1.4),
        Case("L>K/c with E=mc^2 (expect threshold)", E=1.0, L=1.4),
        Case("L>K/c with E>mc^2 (expect scattering)", E=1.2, L=1.4),
        Case("L=K/c with E>0 (critical branch)", E=1.2, L=1.0),
        Case("L<K/c with E>0 (expect spiral/plunge)", E=1.2, L=0.8),
    ]
    for case in cases:
        classify(case)


if __name__ == "__main__":
    main()

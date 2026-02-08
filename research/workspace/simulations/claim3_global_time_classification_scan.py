#!/usr/bin/env python3.12
"""Global-time branch diagnostics for Claim 3 (SR Coulomb).

Run:
  python3.12 research/workspace/simulations/claim3_global_time_classification_scan.py
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
    A = (case.E * case.E - (case.m * case.c * case.c) ** 2) / (case.L * case.L * case.c * case.c)
    B = case.K * case.E / (case.L * case.L * case.c * case.c)
    return alpha2, A, B


def roots_positive_u(alpha2: float, A: float, B: float) -> list[float]:
    eps = 1e-12
    roots: list[float] = []
    if abs(alpha2) <= eps:
        if abs(B) > eps:
            u = -A / (2.0 * B)
            if u >= 0.0:
                roots.append(u)
        return sorted(roots)

    # Q(u)=A+2Bu-alpha2*u^2 = 0 -> alpha2 u^2 -2Bu -A =0
    disc = B * B + alpha2 * A
    if disc < -eps:
        return []
    disc = max(0.0, disc)
    s = math.sqrt(disc)
    u1 = (B - s) / alpha2
    u2 = (B + s) / alpha2
    for u in [u1, u2]:
        if u >= 0.0:
            roots.append(u)
    roots = sorted(roots)
    # dedupe
    ded: list[float] = []
    for u in roots:
        if not ded or abs(u - ded[-1]) > 1e-9:
            ded.append(u)
    return ded


def classify(case: Case) -> None:
    alpha2, A, B = invariants(case)
    roots = roots_positive_u(alpha2, A, B)
    print(case.name)
    print(f"  alpha^2={alpha2:+.6f}, A={A:+.6f}, B={B:+.6f}, positive roots={roots}")

    if alpha2 > 0:
        if len(roots) == 2:
            if A < 0:
                lab = "L>K/c: bounded radial shell (two positive turning points)"
            elif abs(A) < 1e-10:
                lab = "L>K/c: threshold with u=0 root"
            else:
                lab = "L>K/c: scattering-like branch"
        elif len(roots) == 1:
            lab = "L>K/c: one positive turning point (scattering-like)"
        else:
            lab = "L>K/c: no positive turning point"
    elif abs(alpha2) <= 1e-12:
        lab = "L=K/c: critical linear-Q branch (no periodic shell)"
    else:
        lab = "L<K/c: center-access/plunge branch open (no periodic shell)"

    print(f"  classification: {lab}")
    print()


def main() -> None:
    cases = [
        Case("E<mc^2, L>K/c", E=0.8, L=1.4),
        Case("E=mc^2, L>K/c", E=1.0, L=1.4),
        Case("E>mc^2, L>K/c", E=1.2, L=1.4),
        Case("E>0, L=K/c", E=1.2, L=1.0),
        Case("E>0, L<K/c", E=1.2, L=0.8),
    ]
    for c in cases:
        classify(c)


if __name__ == "__main__":
    main()

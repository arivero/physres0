#!/usr/bin/env python3.12
"""Numerical sanity check for Claim 4 (n=3 Duffing phase portrait).

Equation:
  u'' + a u = b u^3
with b > 0 and physical branch u > 0 (u = 1/r).

This script illustrates:
  - exact circular tuning at u = sqrt(a/b),
  - instability under small perturbations,
  - split into escape-like (u -> 0+) and plunge-like (u large).

Run:
  python3.12 research/workspace/simulations/claim4_duffing_n3_portrait_check.py
"""

from __future__ import annotations

import math
from dataclasses import dataclass


def rhs(u: float, up: float, a: float, b: float) -> tuple[float, float]:
    return up, (-a * u + b * u**3)


def step_rk4(u: float, up: float, h: float, a: float, b: float) -> tuple[float, float]:
    k1u, k1v = rhs(u, up, a, b)
    k2u, k2v = rhs(u + 0.5 * h * k1u, up + 0.5 * h * k1v, a, b)
    k3u, k3v = rhs(u + 0.5 * h * k2u, up + 0.5 * h * k2v, a, b)
    k4u, k4v = rhs(u + h * k3u, up + h * k3v, a, b)
    un = u + (h / 6.0) * (k1u + 2.0 * k2u + 2.0 * k3u + k4u)
    vpn = up + (h / 6.0) * (k1v + 2.0 * k2v + 2.0 * k3v + k4v)
    return un, vpn


def energy(u: float, up: float, a: float, b: float) -> float:
    return 0.5 * up * up + 0.5 * a * u * u - 0.25 * b * u**4


@dataclass
class Case:
    name: str
    u0: float
    up0: float


def classify(case: Case, *, a: float, b: float, h: float = 0.002, nsteps: int = 120000) -> None:
    u = case.u0
    up = case.up0
    e0 = energy(u, up, a, b)
    u_min = u
    u_max = u
    status = "undetermined"

    for _ in range(nsteps):
        u_prev = u
        u, up = step_rk4(u, up, h, a, b)
        if u_prev > 0.0 and u <= 0.0:
            u = 0.0
            u_min = min(u_min, u)
            u_max = max(u_max, u)
            status = "escape-like branch (u->0+, r->infinity)"
            break
        u_min = min(u_min, u)
        u_max = max(u_max, u)
        if u >= 6.0:
            status = "plunge-like branch (u large, r->0)"
            break

    if status == "undetermined":
        if abs(u - math.sqrt(a / b)) < 5e-5 and abs(up) < 5e-5:
            status = "circular tuning (near equilibrium)"
        else:
            status = "bounded over horizon (check longer run)"

    e1 = energy(u, up, a, b)
    print(case.name)
    print(f"  init: u0={case.u0:.6f}, up0={case.up0:.6f}, H0={e0:.6f}")
    print(f"  end : u ={u:.6f}, up ={up:.6f}, H1={e1:.6f}, dH={e1 - e0:+.3e}")
    print(f"  range on run: u in [{u_min:.6f}, {u_max:.6f}]")
    print(f"  classification: {status}")
    print()


def main() -> None:
    # Representative normalized parameters a>0, b>0.
    a = 1.0
    b = 1.0
    u_star = math.sqrt(a / b)

    cases = [
        Case("Exact circular point", u_star, 0.0),
        Case("Small outward perturbation (below u*)", u_star * 0.995, 0.0),
        Case("Small inward perturbation (above u*)", u_star * 1.005, 0.0),
        Case("Generic noncircular initial data", 0.35, 0.25),
    ]

    print(f"Parameters: a={a}, b={b}, u*={u_star:.6f}")
    print()
    for case in cases:
        classify(case, a=a, b=b)


if __name__ == "__main__":
    main()

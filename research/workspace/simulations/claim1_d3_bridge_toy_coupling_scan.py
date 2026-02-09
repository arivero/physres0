#!/usr/bin/env python3.12
"""Claim 1 AS toy scan: weak-coupling bridge from ultralocal point.

This is a finite-dimensional two-site surrogate for the d=3 bridge class.

Run:
  python3.12 research/workspace/simulations/claim1_d3_bridge_toy_coupling_scan.py
"""

from __future__ import annotations

import numpy as np


def trap(y: np.ndarray, x: np.ndarray) -> complex:
    t = getattr(np, "trapezoid", None)
    if t is None:
        raise RuntimeError("numpy.trapezoid required")
    return t(y, x)


def onsite(u: np.ndarray, m2: float, lam: float) -> np.ndarray:
    return 0.5 * m2 * (u**2) + 0.25 * lam * (u**4)


def omega_two_site(
    c: complex,
    kappa: float,
    m2: float,
    lam: float,
    grid: np.ndarray,
) -> complex:
    x = grid[:, None]
    y = grid[None, :]
    s = onsite(x, m2, lam) + onsite(y, m2, lam) + 0.5 * kappa * (x - y) ** 2
    w = np.exp(-c * s)
    # Local cylinder observable surrogate: F(x,y)=x^2 + 0.2 y^2.
    f = x**2 + 0.2 * y**2
    num = trap(trap(w * f, grid), grid)
    den = trap(trap(w, grid), grid)
    return num / den


def main() -> None:
    grid = np.linspace(-5.0, 5.0, 801)
    c = 0.9 + 0.0j
    m2 = 1.3
    lam = 0.7
    kappas = [0.0, 0.02, 0.05, 0.08, 0.12, 0.16, 0.20]

    vals = []
    print("Claim 1 AS toy weak-coupling scan (two-site surrogate)")
    print(f"c={c}, m2={m2}, lambda={lam}")
    print()
    for kappa in kappas:
        val = omega_two_site(c, kappa, m2, lam, grid)
        vals.append(val)
        print(f"kappa={kappa:>4.2f}  omega={val.real:+.10f}{val.imag:+.10f}i")
    print()

    base = vals[0]
    print("Departure from ultralocal point (kappa=0):")
    for kappa, val in zip(kappas[1:], vals[1:]):
        diff = abs(val - base)
        ratio = diff / kappa
        print(f"kappa={kappa:>4.2f}  |omega(k)-omega(0)|={diff:.6e}  diff/kappa={ratio:.6e}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3.12
"""Numerical sanity checks for Claim 6 Schwarzschild fixed-energy interval.

Conventions: geometric units G=c=M=1.

Run:
  python3.12 research/workspace/simulations/claim6_schwarzschild_interval_scan.py
"""

from __future__ import annotations

import math


def veff(r: float, ell: float) -> float:
    return (1.0 - 2.0 / r) * (1.0 + (ell * ell) / (r * r))


def circular_u_roots_from_E(E: float) -> tuple[float, float] | None:
    e2 = E * E
    disc = e2 * (9.0 * e2 - 8.0)
    if disc < 0.0:
        return None
    s = math.sqrt(max(0.0, disc))
    u_st = (4.0 - 3.0 * e2 - s) / 8.0
    u_un = (4.0 - 3.0 * e2 + s) / 8.0
    return u_st, u_un


def ell_from_u(u: float) -> float:
    return math.sqrt(1.0 / (u * (1.0 - 3.0 * u)))


def extrema_radii_from_ell(ell: float) -> tuple[float, float] | None:
    l2 = ell * ell
    if l2 < 12.0:
        return None
    s = math.sqrt(l2 - 12.0)
    # Unstable (inner), stable (outer)
    r_un = 0.5 * (l2 - ell * s)
    r_st = 0.5 * (l2 + ell * s)
    return r_un, r_st


def report(E: float) -> None:
    print(f"E={E:.6f}")
    roots = circular_u_roots_from_E(E)
    if roots is None:
        print("  no circular roots (E^2 < 8/9), no bound-shell interval")
        print()
        return

    u_st, u_un = roots
    r_st, r_un = 1.0 / u_st, 1.0 / u_un
    ell_max = ell_from_u(u_st)
    ell_min = ell_from_u(u_un)

    e2 = E * E
    e2_st = veff(r_st, ell_max)
    e2_un = veff(r_un, ell_min)

    print(f"  r_st={r_st:.6f}, r_un={r_un:.6f}")
    print(f"  ell_min(E)={ell_min:.6f}, ell_max(E)={ell_max:.6f}")
    print(f"  check E^2 - Veff(r_st, ell_max) = {e2 - e2_st:+.3e}")
    print(f"  check E^2 - Veff(r_un, ell_min) = {e2 - e2_un:+.3e}")

    ell_mid = 0.5 * (ell_min + ell_max)
    rs = extrema_radii_from_ell(ell_mid)
    if rs is not None:
        r_un_mid, r_st_mid = rs
        vmax = veff(r_un_mid, ell_mid)
        vmin = veff(r_st_mid, ell_mid)
        print(f"  mid-ell={ell_mid:.6f}: Vmin={vmin:.6f}, E^2={e2:.6f}, Vmax={vmax:.6f}")
        if vmin < e2 < vmax:
            print("  interval check: bound shell present (between minimum and maximum)")
        else:
            print("  interval check: outside bound-shell window")
    print()


def main() -> None:
    for E in [math.sqrt(8.0 / 9.0), 0.95, 0.99]:
        report(E)


if __name__ == "__main__":
    main()

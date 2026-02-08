#!/usr/bin/env python3.12
"""Numerical asymptotic check for the Claim 9 screened-Abelian theorem.

Run:
  python3.12 research/workspace/simulations/claim9_abelian_screened_asymptotic_check.py
"""

from __future__ import annotations

import mpmath as mp


def yukawa_green(n: int, m: float, r: float) -> mp.mpf:
    """Fundamental solution of (-Delta + m^2) in R^n at radius r."""
    nu = mp.mpf(n) / 2 - 1
    return (1 / (2 * mp.pi) ** (mp.mpf(n) / 2)) * (m / r) ** nu * mp.besselk(nu, m * r)


def yukawa_asymptotic(n: int, m: float, r: float) -> mp.mpf:
    """Leading large-r asymptotic of yukawa_green."""
    coeff = 1 / (2 * (2 * mp.pi) ** ((mp.mpf(n) - 1) / 2))
    return coeff * m ** ((mp.mpf(n) - 3) / 2) * r ** (-(mp.mpf(n) - 1) / 2) * mp.e ** (-m * r)


def main() -> None:
    mp.mp.dps = 80
    m = mp.mpf("1.3")
    radii = [8.0, 12.0, 16.0, 20.0]
    dims = [2, 3, 4, 5]

    print("Claim 9 screened-Abelian asymptotic ratio check")
    print(f"mass m={m}")
    print()

    for n in dims:
        print(f"n={n} (D={n + 1})")
        last_error = None
        for r in radii:
            exact = yukawa_green(n=n, m=m, r=r)
            lead = yukawa_asymptotic(n=n, m=m, r=r)
            ratio = exact / lead
            error = abs(ratio - 1)
            last_error = error
            print(f"  r={r:>4.1f}  ratio={mp.nstr(ratio, 16)}  |ratio-1|={mp.nstr(error, 5)}")
        if last_error is not None and last_error > mp.mpf("0.05"):
            raise RuntimeError(f"Asymptotic mismatch too large for n={n}: {last_error}")
        print()

    print("All checked dimensions show convergence to the Yukawa asymptotic.")


if __name__ == "__main__":
    main()

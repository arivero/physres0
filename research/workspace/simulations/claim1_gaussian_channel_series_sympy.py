#!/usr/bin/env python3.12
"""Symbolic channel expansion check for Claim 1 Gaussian core.

For F(x)=exp(-alpha*x^2), exact normalized Gaussian oscillatory expectation is
  E_exact = sqrt((-i*lam/(2*eps)) / (alpha - i*lam/(2*eps))).

The channel expansion from exp((i*eps/2)*L) with L=lam^{-1} d^2/dx^2 at x=0 gives
  E_series = sum_{k>=0} ((i*eps/2)^k / k!) * (L^k F)(0).

Run:
  python3.12 research/workspace/simulations/claim1_gaussian_channel_series_sympy.py
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    eps, alpha, lam = sp.symbols("eps alpha lam", positive=True)
    x = sp.symbols("x", real=True)
    i = sp.I

    f = sp.exp(-alpha * x**2)
    L = lambda expr: sp.diff(expr, x, 2) / lam

    exact = sp.sqrt((-i * lam / (2 * eps)) / (alpha - i * lam / (2 * eps)))
    exact_series = sp.series(exact, eps, 0, 6).removeO().expand()

    # Build channel series explicitly up to eps^5
    partial = 0
    expr = f
    for k in range(6):
        if k > 0:
            expr = L(expr)
        partial += ((i * eps / 2) ** k / sp.factorial(k)) * sp.simplify(expr.subs(x, 0))
    partial = sp.expand(sp.simplify(partial))

    diff = sp.expand(sp.simplify(exact_series - partial))

    print("Claim 1 Gaussian channel symbolic check")
    print("Exact series up to eps^5:")
    print(exact_series)
    print("\nChannel series up to eps^5:")
    print(partial)
    print("\nDifference:")
    print(diff)


if __name__ == "__main__":
    main()

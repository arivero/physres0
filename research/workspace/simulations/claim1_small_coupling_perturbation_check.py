#!/usr/bin/env python3.12
"""Numerical checks for Claim 1 Phase I small-coupling closure.

Model:
  weight ~ exp(-(eta - i/eps) * (0.5*lambda*x^2 + g*kappa*x^4))
  with eta > 0 for absolute convergence.

Observable:
  F_m(x) = exp(-alpha * sum_{j=1}^m x_j^2)

Checks:
  1) N-stability for cylinder observables (tail cancellation).
  2) Near-linear O(g) response around g=0.

Run:
  python3.12 research/workspace/simulations/claim1_small_coupling_perturbation_check.py
"""

from __future__ import annotations

import cmath


def simpson_complex(func, a: float, b: float, n_steps: int) -> complex:
    if n_steps % 2:
        n_steps += 1
    h = (b - a) / n_steps
    s = func(a) + func(b)
    for k in range(1, n_steps):
        x = a + k * h
        s += (4 if k % 2 else 2) * func(x)
    return s * (h / 3.0)


class IntegralCache:
    def __init__(self, eps: float, eta: float, x_max: float, n_steps: int) -> None:
        self.eps = eps
        self.eta = eta
        self.x_max = x_max
        self.n_steps = n_steps
        self._cache: dict[tuple[float, float, float, float], complex] = {}

    def one_dim(self, lam: float, kap: float, g: float, alpha: float) -> complex:
        key = (lam, kap, g, alpha)
        if key in self._cache:
            return self._cache[key]
        coeff = self.eta - 1j / self.eps

        def integrand(x: float) -> complex:
            x2 = x * x
            s = 0.5 * lam * x2 + g * kap * x2 * x2
            return cmath.exp(-coeff * s - alpha * x2)

        val = simpson_complex(integrand, -self.x_max, self.x_max, self.n_steps)
        self._cache[key] = val
        return val


def expectation(
    cache: IntegralCache,
    lambdas: list[float],
    kappas: list[float],
    g: float,
    m: int,
    alpha: float,
) -> complex:
    out = 1.0 + 0.0j
    for j, (lam, kap) in enumerate(zip(lambdas, kappas), start=1):
        a = alpha if j <= m else 0.0
        num = cache.one_dim(lam, kap, g, a)
        den = cache.one_dim(lam, kap, g, 0.0)
        out *= num / den
    return out


def max_pairwise_gap(values: list[complex]) -> float:
    worst = 0.0
    for i, a in enumerate(values):
        for b in values[i + 1 :]:
            d = abs(a - b)
            if d > worst:
                worst = d
    return worst


def main() -> None:
    eps = 0.30
    eta = 0.35
    alpha = 0.70
    m = 2

    cache = IntegralCache(eps=eps, eta=eta, x_max=8.0, n_steps=4000)

    # N-stability test: same first m coordinates, variable tails.
    base_lam = [1.00, 1.25]
    base_kap = [0.30, 0.45]
    vals_n = []
    for n in range(m, m + 7):
        tail_lam = [0.95 + 0.05 * ((-1.0) ** j) for j in range(3, n + 1)]
        tail_kap = [0.25 + 0.02 * ((-1.0) ** j) for j in range(3, n + 1)]
        lambdas = base_lam + tail_lam
        kappas = base_kap + tail_kap
        vals_n.append(expectation(cache, lambdas, kappas, g=0.06, m=m, alpha=alpha))

    print("Claim 1 Phase I small-coupling checks")
    print(f"N-stability max pairwise gap : {max_pairwise_gap(vals_n):.3e}")

    # Small-coupling response around g=0.
    g_values = [0.00, 0.02, 0.04, 0.06, 0.08]
    vals_g = []
    for g in g_values:
        vals_g.append(expectation(cache, base_lam, base_kap, g=g, m=m, alpha=alpha))

    ref = vals_g[0]
    print("Small-coupling response:")
    max_slope = 0.0
    for g, val in zip(g_values[1:], vals_g[1:]):
        diff = abs(val - ref)
        slope = diff / g
        if slope > max_slope:
            max_slope = slope
        print(f"  g={g:.2f}: |E(g)-E(0)|={diff:.3e}, |E(g)-E(0)|/g={slope:.3e}")
    print(f"max observed slope bound      : {max_slope:.3e}")


if __name__ == "__main__":
    main()

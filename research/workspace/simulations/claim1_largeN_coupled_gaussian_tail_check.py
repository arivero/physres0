#!/usr/bin/env python3.12
"""Numerical check for Claim 1 Phase N large-N mode-coupled Gaussian-tail lift.

Model (m=1):
  S_N(u, v_2..v_N) = P(u) + sum_{j=2}^N (lambda/2 + a_j u^2) v_j^2
with a_j = a0 / j^2.

After exact Gaussian tail integration:
  weight_N(u) = exp(-(eta - i/eps) P(u)) * prod_{j=2}^N sqrt(lambda/(lambda + 2 a_j u^2)).

We compute
  omega_N(F) = int F(u) weight_N(u) du / int weight_N(u) du
for F(u)=exp(-alpha u^2), and compare |omega_N - omega_ref|
against tail sum sum_{j>N} a_j/lambda.

Run:
  python3.12 research/workspace/simulations/claim1_largeN_coupled_gaussian_tail_check.py
"""

from __future__ import annotations

import cmath
import math


def simpson_complex(func, a: float, b: float, n_steps: int) -> complex:
    if n_steps % 2:
        n_steps += 1
    h = (b - a) / n_steps
    s = func(a) + func(b)
    for k in range(1, n_steps):
        x = a + k * h
        s += (4 if k % 2 else 2) * func(x)
    return s * (h / 3.0)


def p_u(u: float) -> float:
    # Coercive observed-block action.
    return 0.5 * u * u + 0.15 * (u**4)


def tail_factor(u: float, n: int, lam: float, a0: float) -> float:
    val = 1.0
    u2 = u * u
    for j in range(2, n + 1):
        a_j = a0 / (j * j)
        val *= math.sqrt(lam / (lam + 2.0 * a_j * u2))
    return val


def omega_n(
    n: int,
    eps: float,
    eta: float,
    lam: float,
    a0: float,
    alpha: float,
    u_max: float,
    n_steps: int,
) -> complex:
    coeff = eta - 1j / eps

    def w(u: float) -> complex:
        return cmath.exp(-coeff * p_u(u)) * tail_factor(u, n, lam, a0)

    num = simpson_complex(lambda u: cmath.exp(-alpha * u * u) * w(u), -u_max, u_max, n_steps)
    den = simpson_complex(w, -u_max, u_max, n_steps)
    return num / den


def tail_sum(n: int, lam: float, a0: float, n_cap: int = 30000) -> float:
    # Approximate sum_{j>n} a_j / lam with finite cap (sufficient for diagnostics here).
    return sum((a0 / (j * j)) / lam for j in range(n + 1, n_cap + 1))


def main() -> None:
    eps = 0.30
    eta = 0.45
    lam = 1.0
    a0 = 0.8
    alpha = 0.7
    u_max = 7.0
    n_steps = 4000

    n_values = [4, 6, 8, 12, 16, 24, 32, 48]
    n_ref = 72

    ref = omega_n(n_ref, eps, eta, lam, a0, alpha, u_max, n_steps)

    print("Claim 1 Phase N large-N coupled Gaussian-tail check")
    print(f"reference N={n_ref}: {ref.real:+.12f}{ref.imag:+.12f}i")
    print("N   |omega_N-ref|     tail_sum(N)")
    for n in n_values:
        val = omega_n(n, eps, eta, lam, a0, alpha, u_max, n_steps)
        err = abs(val - ref)
        ts = tail_sum(n, lam, a0)
        print(f"{n:2d}  {err: .6e}   {ts: .6e}")


if __name__ == "__main__":
    main()

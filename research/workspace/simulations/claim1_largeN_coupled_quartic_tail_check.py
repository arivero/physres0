#!/usr/bin/env python3.12
"""Numerical check for Claim 1 Phase T (large-N coupled quartic tails).

Model (m=1):
  S_N(u, v_2..v_N)
    = P(u) + sum_{j=2}^N [ (lam/2 + a_j u^2) v_j^2 + gamma v_j^4 ]
  a_j = a0 / j^2

After integrating each tail mode:
  R_j(u) = I_j(a_j u^2) / I_j(0),
  I_j(b) = int exp(-(eta - i/eps)*((lam/2 + b)t^2 + gamma t^4)) dt

We compute omega_N(F) with F(u)=exp(-alpha u^2) and show convergence with N.

Run:
  python3.12 research/workspace/simulations/claim1_largeN_coupled_quartic_tail_check.py
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
    return 0.55 * u * u + 0.10 * (u**4)


def i_j(
    b: float,
    coeff: complex,
    lam: float,
    gamma: float,
    t_max: float,
    n_t: int,
) -> complex:
    return simpson_complex(
        lambda t: cmath.exp(-coeff * ((0.5 * lam + b) * t * t + gamma * (t**4))),
        -t_max,
        t_max,
        n_t,
    )


def main() -> None:
    eps = 0.40
    eta = 0.55
    coeff = eta - 1j / eps
    lam = 1.15
    gamma = 0.35
    a0 = 0.80
    alpha = 0.70

    n_ref = 14
    n_values = [4, 6, 8, 10, 12]

    u_max = 4.5
    n_u = 140
    t_max = 6.0
    n_t = 900

    # Precompute quadrature grid/weights for u integration.
    h_u = (2.0 * u_max) / n_u
    u_grid = [-u_max + k * h_u for k in range(n_u + 1)]
    w_u = [1 if (k == 0 or k == n_u) else (4 if k % 2 else 2) for k in range(n_u + 1)]

    # Precompute baseline I_j(0).
    i0 = {}
    for j in range(2, n_ref + 1):
        i0[j] = i_j(0.0, coeff, lam, gamma, t_max, n_t)

    # Precompute mode ratios R_j(u_k).
    ratios = {j: [] for j in range(2, n_ref + 1)}
    for u in u_grid:
        u2 = u * u
        for j in range(2, n_ref + 1):
            a_j = a0 / (j * j)
            b = a_j * u2
            ratios[j].append(i_j(b, coeff, lam, gamma, t_max, n_t) / i0[j])

    def omega_n(n: int) -> complex:
        num = 0.0 + 0.0j
        den = 0.0 + 0.0j
        for k, u in enumerate(u_grid):
            prod = 1.0 + 0.0j
            for j in range(2, n + 1):
                prod *= ratios[j][k]
            base = cmath.exp(-coeff * p_u(u))
            obs = math.exp(-alpha * u * u)
            term_num = base * obs * prod
            term_den = base * prod
            num += w_u[k] * term_num
            den += w_u[k] * term_den
        num *= h_u / 3.0
        den *= h_u / 3.0
        return num / den

    ref = omega_n(n_ref)
    print("Claim 1 Phase T large-N coupled quartic-tail check")
    print(f"reference N={n_ref}: {ref.real:+.12f}{ref.imag:+.12f}i")
    print("N   |omega_N-ref|     tail sum sum_{j>N} a_j")
    for n in n_values:
        val = omega_n(n)
        err = abs(val - ref)
        tail = sum(a0 / (j * j) for j in range(n + 1, 4000))
        print(f"{n:2d}  {err: .6e}   {tail: .6e}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3.12
"""Finite-dimensional Schwinger-Dyson identity check (Claim 1 Phase Q).

Identity in 1D:
  I_c[V S' F] = (1/c) I_c[(V F)']
with I_c[G] = ∫ exp(-(eta - i/eps) S(x)) G(x) dx.

We test:
  1) constant vector field V=1, nontrivial F
  2) nonconstant V(x)=1+nu x^2, nontrivial F
  3) special case F=1, V=1 => omega_c[S'] = 0

Run:
  python3.12 research/workspace/simulations/claim1_fd_schwinger_dyson_check.py
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


def s_of_x(x: float, lam: float, kap: float, g: float) -> float:
    x2 = x * x
    return 0.5 * lam * x2 + g * kap * x2 * x2


def ds_of_x(x: float, lam: float, kap: float, g: float) -> float:
    return lam * x + 4.0 * g * kap * (x**3)


def check_case(
    eps: float,
    eta: float,
    lam: float,
    kap: float,
    g: float,
    nu: float,
    alpha: float,
    x_max: float,
    n_steps: int,
) -> None:
    c = eta - 1j / eps

    def w(x: float) -> complex:
        return cmath.exp(-c * s_of_x(x, lam, kap, g))

    def f(x: float) -> float:
        return cmath.exp(-alpha * x * x).real

    def df(x: float) -> float:
        return -2.0 * alpha * x * f(x)

    def v_const(x: float) -> float:
        return 1.0

    def dv_const(_: float) -> float:
        return 0.0

    def v_poly(x: float) -> float:
        return 1.0 + nu * x * x

    def dv_poly(x: float) -> float:
        return 2.0 * nu * x

    def run(v, dv, label: str) -> None:
        lhs = simpson_complex(
            lambda x: w(x) * v(x) * ds_of_x(x, lam, kap, g) * f(x),
            -x_max,
            x_max,
            n_steps,
        )
        rhs = (1.0 / c) * simpson_complex(
            lambda x: w(x) * (dv(x) * f(x) + v(x) * df(x)),
            -x_max,
            x_max,
            n_steps,
        )
        err = abs(lhs - rhs)
        scale = max(1.0, abs(lhs), abs(rhs))
        print(f"{label}: abs err={err:.3e}, rel err={err/scale:.3e}")

    print("Schwinger-Dyson raw-identity checks")
    run(v_const, dv_const, "V=1")
    run(v_poly, dv_poly, "V=1+nu x^2")

    z = simpson_complex(w, -x_max, x_max, n_steps)
    mean_ds = simpson_complex(
        lambda x: w(x) * ds_of_x(x, lam, kap, g),
        -x_max,
        x_max,
        n_steps,
    ) / z
    print(f"omega_c[S'] with F=1,V=1: {mean_ds.real:+.3e}{mean_ds.imag:+.3e}i")


def main() -> None:
    eps = 0.38
    eta = 0.48
    lam = 1.2
    kap = 0.9
    g = 0.55
    nu = 0.35
    alpha = 0.65
    x_max = 8.0
    n_steps = 8000

    check_case(eps, eta, lam, kap, g, nu, alpha, x_max, n_steps)


if __name__ == "__main__":
    main()

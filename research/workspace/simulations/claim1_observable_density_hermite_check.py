#!/usr/bin/env python3.12
"""Observable-class density check for Claim 1 Phase P.

We test convergence of normalized oscillatory expectations
  omega(F_N) -> omega(F)
for a Schwartz target
  F(x) = exp(-x^2) * cos(x),
with polynomial-Gaussian approximants
  F_N(x) = exp(-x^2) * sum_{k=0}^N (-1)^k x^(2k)/(2k)!.

Each F_N belongs to the Gaussian-exponential polynomial span, and this
sequence converges rapidly to F on R.

Run:
  python3.12 research/workspace/simulations/claim1_observable_density_hermite_check.py
"""

from __future__ import annotations

import mpmath as mp


def s_x(x: mp.mpf, lam: mp.mpf, kap: mp.mpf, g: mp.mpf) -> mp.mpf:
    return mp.mpf("0.5") * lam * x * x + g * kap * (x**4)


def cos_taylor_even(x: mp.mpf, n: int) -> mp.mpf:
    out = mp.mpf("0.0")
    x2 = x * x
    power = mp.mpf("1.0")
    fact = mp.mpf("1.0")
    sign = mp.mpf("1.0")
    for k in range(n + 1):
        if k > 0:
            power *= x2
            fact *= (2 * k - 1) * (2 * k)
            sign = -sign
        out += sign * power / fact
    return out


def omega(
    f,
    eps: mp.mpf,
    eta: mp.mpf,
    lam: mp.mpf,
    kap: mp.mpf,
    g: mp.mpf,
) -> complex:
    coeff = eta - (1j / eps)

    def w(x):
        return mp.e ** (-coeff * s_x(x, lam, kap, g))

    num = mp.quad(lambda t: w(t) * f(t), [-mp.inf, mp.inf])
    den = mp.quad(lambda t: w(t), [-mp.inf, mp.inf])
    return complex(num / den)


def main() -> None:
    mp.mp.dps = 60
    eps = mp.mpf("0.35")
    eta = mp.mpf("0.5")
    lam = mp.mpf("1.1")
    kap = mp.mpf("0.8")
    g = mp.mpf("0.45")

    def f_target(x):
        return mp.e ** (-(x * x)) * mp.cos(x)

    omega_target = omega(f_target, eps, eta, lam, kap, g)

    print("Claim 1 Phase P observable density check")
    print(
        "target omega(F) = "
        f"{omega_target.real:+.12f}{omega_target.imag:+.12f}i"
    )
    print("N   |omega(F_N)-omega(F)|")

    for n in [0, 1, 2, 3, 4, 6, 8, 10, 12]:
        def f_n(x, nn=n):
            return mp.e ** (-(x * x)) * cos_taylor_even(x, nn)

        val = omega(f_n, eps, eta, lam, kap, g)
        err = abs(val - omega_target)
        print(f"{n:2d}   {err:.6e}")


if __name__ == "__main__":
    main()

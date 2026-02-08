#!/usr/bin/env python3.12
"""Numerical eta->0+ check for a quartic block using contour target at eta=0.

Block integral:
  I_eta(alpha) = ∫ exp(-(eta - i/eps)*(0.5*lam*x^2 + g*kap*x^4) - alpha*x^2) dx

For eta=0 we evaluate along rotated contour x = exp(i*pi/8) y.
For eta>0 we evaluate on real axis.
We compare normalized expectations E_eta = I_eta(alpha)/I_eta(0).

Run:
  python3.12 research/workspace/simulations/claim1_eta_zero_quartic_block_check.py
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
        y = a + k * h
        s += (4 if k % 2 else 2) * func(y)
    return s * (h / 3.0)


def block_integral(
    alpha: float,
    eta: float,
    eps: float,
    lam: float,
    kap: float,
    g: float,
    theta: float,
    y_max: float,
    n_steps: int,
) -> complex:
    phase = cmath.exp(1j * theta)
    prefactor = eta - 1j / eps

    def integrand(y: float) -> complex:
        x = phase * y
        s = 0.5 * lam * x * x + g * kap * x * x * x * x
        return cmath.exp(-prefactor * s - alpha * x * x) * phase

    return simpson_complex(integrand, -y_max, y_max, n_steps)


def expectation(
    eta: float,
    eps: float,
    lam: float,
    kap: float,
    g: float,
    alpha: float,
    theta: float,
    y_max: float,
    n_steps: int,
) -> complex:
    num = block_integral(alpha, eta, eps, lam, kap, g, theta, y_max, n_steps)
    den = block_integral(0.0, eta, eps, lam, kap, g, theta, y_max, n_steps)
    return num / den


def main() -> None:
    eps = 0.35
    lam = 1.10
    kap = 0.75
    g = 0.40
    alpha = 0.60
    y_max = 6.0
    n_steps = 6000

    theta_rot = math.pi / 8.0

    # eta=0 contour target
    e0 = expectation(
        eta=0.0,
        eps=eps,
        lam=lam,
        kap=kap,
        g=g,
        alpha=alpha,
        theta=theta_rot,
        y_max=y_max,
        n_steps=n_steps,
    )

    print("Claim 1 Phase K quartic eta->0 check")
    print(f"eta=0 contour target: {e0.real:+.10f}{e0.imag:+.10f}i")

    for eta in [0.40, 0.25, 0.15, 0.10, 0.07, 0.05, 0.03, 0.02]:
        e_eta = expectation(
            eta=eta,
            eps=eps,
            lam=lam,
            kap=kap,
            g=g,
            alpha=alpha,
            theta=0.0,
            y_max=y_max,
            n_steps=n_steps,
        )
        err = abs(e_eta - e0)
        print(
            f"  eta={eta:>4.2f}: E_eta={e_eta.real:+.10f}{e_eta.imag:+.10f}i, "
            f"|E_eta-E0|={err:.3e}"
        )


if __name__ == "__main__":
    main()

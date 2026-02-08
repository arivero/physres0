#!/usr/bin/env python3.12
"""Numerical eta->0+ check for a coupled (non-factorized) quartic 2D block.

Integral:
  I_eta(a1,a2) = ∬ exp(-(eta - i/eps)*(Q2 + g*Q4) - a1*x1^2 - a2*x2^2) dx1 dx2
with
  Q2 = 0.5*(lam1*x1^2 + lam2*x2^2)
  Q4 = kap1*x1^4 + kap2*x2^4 + mu*x1^2*x2^2

For eta=0 target, we integrate along rotated contour x_j = exp(i*pi/8) y_j.
For eta>0 we evaluate on the same rotated contour (the contour used in the theorem proof).

Run:
  python3.12 research/workspace/simulations/claim1_eta_zero_coupled_quartic_block_check.py
"""

from __future__ import annotations

import cmath
import math


def block_integral_2d(
    alpha1: float,
    alpha2: float,
    eta: float,
    theta: float,
    eps: float,
    lam1: float,
    lam2: float,
    kap1: float,
    kap2: float,
    mu: float,
    g: float,
    y_max: float,
    n_grid: int,
) -> complex:
    phase = cmath.exp(1j * theta)
    jac = phase * phase
    dy = (2.0 * y_max) / n_grid
    pref = eta - 1j / eps
    acc = 0.0 + 0.0j

    for i in range(n_grid):
        y1 = -y_max + (i + 0.5) * dy
        x1 = phase * y1
        x1_2 = x1 * x1
        x1_4 = x1_2 * x1_2
        for j in range(n_grid):
            y2 = -y_max + (j + 0.5) * dy
            x2 = phase * y2
            x2_2 = x2 * x2
            x2_4 = x2_2 * x2_2

            q2 = 0.5 * (lam1 * x1_2 + lam2 * x2_2)
            q4 = kap1 * x1_4 + kap2 * x2_4 + mu * x1_2 * x2_2
            expo = -pref * (q2 + g * q4) - alpha1 * x1_2 - alpha2 * x2_2
            acc += cmath.exp(expo)

    return acc * jac * (dy * dy)


def expectation_2d(
    alpha1: float,
    alpha2: float,
    eta: float,
    theta: float,
    eps: float,
    lam1: float,
    lam2: float,
    kap1: float,
    kap2: float,
    mu: float,
    g: float,
    y_max: float,
    n_grid: int,
) -> complex:
    num = block_integral_2d(
        alpha1,
        alpha2,
        eta,
        theta,
        eps,
        lam1,
        lam2,
        kap1,
        kap2,
        mu,
        g,
        y_max,
        n_grid,
    )
    den = block_integral_2d(
        0.0,
        0.0,
        eta,
        theta,
        eps,
        lam1,
        lam2,
        kap1,
        kap2,
        mu,
        g,
        y_max,
        n_grid,
    )
    return num / den


def main() -> None:
    eps = 0.33
    lam1, lam2 = 1.00, 1.20
    kap1, kap2 = 0.70, 0.55
    mu = 0.60
    g = 0.45
    alpha1, alpha2 = 0.55, 0.35
    y_max = 3.8
    n_grid = 160
    theta_rot = math.pi / 8.0

    e0 = expectation_2d(
        alpha1,
        alpha2,
        eta=0.0,
        theta=theta_rot,
        eps=eps,
        lam1=lam1,
        lam2=lam2,
        kap1=kap1,
        kap2=kap2,
        mu=mu,
        g=g,
        y_max=y_max,
        n_grid=n_grid,
    )

    print("Claim 1 Phase L coupled quartic eta->0 check")
    print(f"eta=0 contour target: {e0.real:+.10f}{e0.imag:+.10f}i")
    for eta in [0.35, 0.20, 0.12, 0.08, 0.05, 0.03, 0.02]:
        e_eta = expectation_2d(
            alpha1,
            alpha2,
            eta=eta,
            theta=theta_rot,
            eps=eps,
            lam1=lam1,
            lam2=lam2,
            kap1=kap1,
            kap2=kap2,
            mu=mu,
            g=g,
            y_max=y_max,
            n_grid=n_grid,
        )
        err = abs(e_eta - e0)
        print(
            f"  eta={eta:>4.2f}: E_eta={e_eta.real:+.10f}{e_eta.imag:+.10f}i, "
            f"|E_eta-E0|={err:.3e}"
        )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3.12
"""Check scale-flow covariance for Claim 1 Phase R.

Invariant transform:
  (kappa, eta, h) -> (mu*kappa, eta/mu, mu*h)
keeps
  (eta - i/h)*kappa
exactly invariant, so normalized oscillatory expectations must match.

Run:
  python3.12 research/workspace/simulations/claim1_scale_flow_covariance_check.py
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


def s_of_x(x: float) -> float:
    x2 = x * x
    return 0.6 * x2 + 0.35 * x2 * x2


def omega(kappa: float, eta: float, hbar: float, alpha: float, x_max: float, n_steps: int) -> complex:
    coeff = (eta - 1j / hbar) * kappa

    def w(x: float) -> complex:
        return cmath.exp(-coeff * s_of_x(x))

    num = simpson_complex(lambda x: w(x) * cmath.exp(-alpha * x * x), -x_max, x_max, n_steps)
    den = simpson_complex(w, -x_max, x_max, n_steps)
    return num / den


def main() -> None:
    kappa = 1.4
    eta = 0.55
    hbar = 0.37
    alpha = 0.8
    mu = 2.7
    x_max = 7.5
    n_steps = 8000

    val = omega(kappa, eta, hbar, alpha, x_max, n_steps)
    val_tau = omega(mu * kappa, eta / mu, mu * hbar, alpha, x_max, n_steps)

    err = abs(val - val_tau)
    scale = max(1.0, abs(val), abs(val_tau))
    print("Claim 1 Phase R scale-flow covariance check")
    print(f"omega base : {val.real:+.12f}{val.imag:+.12f}i")
    print(f"omega tau  : {val_tau.real:+.12f}{val_tau.imag:+.12f}i")
    print(f"abs error  : {err:.3e}")
    print(f"rel error  : {err/scale:.3e}")


if __name__ == "__main__":
    main()

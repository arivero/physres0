#!/usr/bin/env python3.12
"""Check non-vanishing lower bounds for oscillatory partition factors (Phase O).

Model:
  S(x) = 0.5*lam*x^2 + g*kap*x^4
  A_eta = ∫ exp(-eta*S) dx
  Z_eps = ∫ exp(-(eta - i/eps)*S) dx

Bounds:
  |Z_eps| >= A_eta * (1 - M1/eps),   M1 = E_{mu_eta}[|S|]
  |Z_eps| >= A_eta * (1 - M2/(2 eps^2)), M2 = E_{mu_eta}[S^2]

Run:
  python3.12 research/workspace/simulations/claim1_partition_nonvanishing_bound_check.py
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


def main() -> None:
    lam = 1.1
    kap = 0.8
    g = 0.5
    eta = 0.45
    x_max = 8.0
    n_steps = 8000

    def a_integrand(x: float) -> complex:
        return cmath.exp(-eta * s_of_x(x, lam, kap, g))

    A_eta = simpson_complex(a_integrand, -x_max, x_max, n_steps).real

    m1_num = simpson_complex(
        lambda x: s_of_x(x, lam, kap, g) * cmath.exp(-eta * s_of_x(x, lam, kap, g)),
        -x_max,
        x_max,
        n_steps,
    ).real
    M1 = m1_num / A_eta

    m2_num = simpson_complex(
        lambda x: (s_of_x(x, lam, kap, g) ** 2) * cmath.exp(-eta * s_of_x(x, lam, kap, g)),
        -x_max,
        x_max,
        n_steps,
    ).real
    M2 = m2_num / A_eta

    print("Claim 1 Phase O non-vanishing partition bound check")
    print(f"A_eta = {A_eta:.8e}, M1 = {M1:.8e}, M2 = {M2:.8e}")
    print("eps   |Z|            LB1            LB2")
    for eps in [0.5, 0.8, 1.0, 1.5, 2.0, 3.0]:
        Z = simpson_complex(
            lambda x: cmath.exp(
                -(eta - 1j / eps) * s_of_x(x, lam, kap, g)
            ),
            -x_max,
            x_max,
            n_steps,
        )
        abs_z = abs(Z)
        lb1 = max(0.0, A_eta * (1.0 - M1 / eps))
        lb2 = max(0.0, A_eta * (1.0 - M2 / (2.0 * eps * eps)))
        print(f"{eps:>3.1f}  {abs_z: .8e}  {lb1: .8e}  {lb2: .8e}")


if __name__ == "__main__":
    main()

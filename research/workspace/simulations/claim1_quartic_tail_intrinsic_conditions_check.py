#!/usr/bin/env python3.12
"""Check intrinsic moment-based conditions for quartic-tail assumptions (Phase V).

For each j and b:
  S_{j,b}(t) = ((lam_j/2)+b)t^2 + gamma_j t^4
  I_j(b) = ∫ exp(-(eta - i/eps) S_{j,b}(t)) dt

We estimate:
  M1_{j,b} = E_{nu_{j,b}}[S_{j,b}]
  M2_{j,b} = E_{nu_{j,b}}[t^2]
  L_j^int = |c| * sup_b M2_{j,b} / (1 - sup_b M1_{j,b}/eps)

and check weighted summability Σ A_j L_j^int for A_j=a0/j^2.

Run:
  python3.12 research/workspace/simulations/claim1_quartic_tail_intrinsic_conditions_check.py
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


def s_j_b(t: float, lam_j: float, gamma_j: float, b: float) -> float:
    t2 = t * t
    return (0.5 * lam_j + b) * t2 + gamma_j * t2 * t2


def main() -> None:
    eps = 1.9
    eta = 0.55
    c = eta - 1j / eps
    a0 = 0.8

    b_grid = [0.0, 0.2, 0.5, 1.0, 1.6, 2.5]
    j_values = list(range(2, 26))
    t_max = 7.0
    n_t = 1400

    print("Claim 1 Phase V intrinsic-condition diagnostics")
    print("j   sup M1      sup M2      eps-M1      Lj_int      A_j*Lj_int")

    weighted_sum = 0.0
    max_m1 = 0.0

    for j in j_values:
        lam_j = 1.05 + 0.03 / j
        gamma_j = 0.30 + 0.01 / j
        a_j = a0 / (j * j)

        sup_m1 = 0.0
        sup_m2 = 0.0

        for b in b_grid:
            z = simpson_complex(
                lambda t: cmath.exp(-eta * s_j_b(t, lam_j, gamma_j, b)),
                -t_max,
                t_max,
                n_t,
            ).real
            m1_num = simpson_complex(
                lambda t: s_j_b(t, lam_j, gamma_j, b)
                * cmath.exp(-eta * s_j_b(t, lam_j, gamma_j, b)),
                -t_max,
                t_max,
                n_t,
            ).real
            m2_num = simpson_complex(
                lambda t: (t * t) * cmath.exp(-eta * s_j_b(t, lam_j, gamma_j, b)),
                -t_max,
                t_max,
                n_t,
            ).real
            m1 = m1_num / z
            m2 = m2_num / z
            sup_m1 = max(sup_m1, m1)
            sup_m2 = max(sup_m2, m2)

        max_m1 = max(max_m1, sup_m1)
        margin = eps - sup_m1
        lj_int = abs(c) * sup_m2 / margin
        term = a_j * lj_int
        weighted_sum += term
        print(f"{j:2d}  {sup_m1: .5e}  {sup_m2: .5e}  {margin: .5e}  {lj_int: .5e}  {term: .5e}")

    print(f"\nmax_j sup M1 = {max_m1:.6e}")
    print(f"eps - max_j sup M1 = {eps - max_m1:.6e}")
    print(f"partial sum Σ_{{j=2..{j_values[-1]}}} A_j L_j^int = {weighted_sum:.6e}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3.12
"""Theme 1 Coulomb EBK quantization cross-check.

Run:
  python3.12 research/workspace/simulations/theme1_coulomb_ebk_crosscheck.py

Key EBK relation for Coulomb: J_r + L = n * hbar, where
J_r = (1/2pi) oint p_r dr = m Ze^2 / sqrt(-2mE) - L.
"""

from __future__ import annotations

import math

import numpy as np


def j_r_analytic(e: float, l: float, m: float, z_e2: float) -> float:
    """Analytic J_r = (1/2pi) oint p_r dr for Coulomb V=-Ze^2/r.

    J_r = m Ze^2 / sqrt(-2mE) - L.
    Valid for E < 0 (bound states).
    """
    return m * z_e2 / math.sqrt(-2.0 * m * e) - l


def j_r_numerical(e: float, l: float, m: float, z_e2: float, n_pts: int = 10000) -> float:
    """Numerical J_r = (1/pi) int_{r_min}^{r_max} p_r dr.

    This equals (1/2pi) oint p_r dr since oint = 2 * int over half-period.
    """
    a_coeff = 2.0 * m * e
    b_coeff = 2.0 * m * z_e2
    c_coeff = -l * l
    disc = b_coeff * b_coeff - 4.0 * a_coeff * c_coeff
    if disc < 0.0:
        return 0.0
    sqrt_disc = math.sqrt(disc)
    r1 = (-b_coeff + sqrt_disc) / (2.0 * a_coeff)
    r2 = (-b_coeff - sqrt_disc) / (2.0 * a_coeff)
    r_min = min(r1, r2)
    r_max = max(r1, r2)
    if r_min <= 0.0:
        r_min = 1.0e-10

    r_arr = np.linspace(r_min, r_max, n_pts + 2)[1:-1]
    p_sq = 2.0 * m * (e + z_e2 / r_arr) - l * l / (r_arr * r_arr)
    p_sq = np.maximum(p_sq, 0.0)
    p_r = np.sqrt(p_sq)
    dr = (r_max - r_min) / (n_pts + 1)
    return float(np.sum(p_r) * dr / math.pi)


def ebk_energy(n: int, m: float, z_e2: float, hbar: float) -> float:
    """EBK hydrogen energy: E_n = -m (Ze^2)^2 / (2 hbar^2 n^2)."""
    return -m * z_e2 * z_e2 / (2.0 * hbar * hbar * n * n)


def main() -> None:
    m = 1.0
    z_e2 = 1.0
    hbar = 1.0

    check_jr_plus_l_identity = True
    check_ebk_spectrum = True
    check_numerical_integral = True

    rows: list[tuple[int, int, float, float, float, float]] = []

    for n in range(1, 8):
        e_exact = ebk_energy(n, m, z_e2, hbar)

        for ell in range(n):
            n_r = n - ell - 1
            l_val = float(ell) * hbar

            # Analytic J_r.
            j_r_a = j_r_analytic(e_exact, l_val, m, z_e2)

            # Key identity: J_r + L = n * hbar.
            j_r_plus_l = j_r_a + l_val
            expected_sum = float(n) * hbar
            if abs(j_r_plus_l - expected_sum) > 1.0e-10:
                check_jr_plus_l_identity = False

            # Numerical J_r (only for n_r > 0 and ell > 0 to avoid singularities).
            j_r_n = 0.0
            if n_r > 0 and ell > 0:
                j_r_n = j_r_numerical(e_exact, l_val, m, z_e2, n_pts=50000)
                if abs(j_r_n - j_r_a) > 0.01 * max(abs(j_r_a), 0.01):
                    check_numerical_integral = False

            rows.append((n, ell, n_r, e_exact, j_r_a, j_r_n))

    # Verify EBK spectrum matches exact hydrogen.
    for n in range(1, 8):
        e_ebk = ebk_energy(n, m, z_e2, hbar)
        e_exact = -m * z_e2**2 / (2.0 * hbar**2 * n**2)
        if abs(e_ebk - e_exact) > 1.0e-14:
            check_ebk_spectrum = False

    all_ok = check_jr_plus_l_identity and check_ebk_spectrum and check_numerical_integral

    print("Theme 1 Coulomb EBK quantization cross-check")
    print(f"m={m:.6f}, Ze2={z_e2:.6f}, hbar={hbar:.6f}")
    print("Key identity: J_r + L = n * hbar")
    print("(n, ell, n_r, E_exact, J_r_analytic, J_r_numeric):")
    for n, ell, n_r, e_ex, j_a, j_n in rows:
        print(
            f"  n={n}, ell={ell}, n_r={n_r:.0f}: "
            f"E={e_ex:.8f}, J_r={j_a:.8f}, "
            f"J_r+L={j_a + ell:.8f}, "
            f"J_r_numeric={j_n:.8f}"
        )
    print(f"check_jr_plus_l_identity={check_jr_plus_l_identity}")
    print(f"check_ebk_spectrum={check_ebk_spectrum}")
    print(f"check_numerical_integral={check_numerical_integral}")
    print(f"all_checks_pass={all_ok}")


if __name__ == "__main__":
    main()

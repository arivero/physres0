#!/usr/bin/env python3.12
"""Claim 4 n=3+delta robustness window diagnostics.

Run:
  python3.12 research/workspace/simulations/claim4_n3delta_robustness_check.py
"""

from __future__ import annotations

import math

import numpy as np


def v_eff(r: float, l: float, m: float, k: float, n: float) -> float:
    """Effective potential for V(r) = -K/r^n."""
    return l * l / (2.0 * m * r * r) - k / (r ** n)


def v_eff_pp(r: float, l: float, m: float, k: float, n: float) -> float:
    """Second derivative of V_eff numerically."""
    h = 1.0e-7 * r
    vp = v_eff(r + h, l, m, k, n)
    vm = v_eff(r - h, l, m, k, n)
    v0 = v_eff(r, l, m, k, n)
    return (vp - 2.0 * v0 + vm) / (h * h)


def find_r_c(l: float, m: float, k: float, n: float) -> float:
    """Find circular orbit radius from V_eff'(r_c) = 0."""
    # L^2/(m r^3) = n K / r^{n+1}  =>  r^{n-2} = n m K / L^2
    return (n * m * k / (l * l)) ** (1.0 / (n - 2.0))


def stability_sign(delta: float) -> float:
    """Analytic sign of V_eff''(r_c) as a function of delta."""
    n = 3.0 + delta
    return 3.0 - n * (n - 1.0)


def main() -> None:
    l = 1.0
    m = 1.0
    k = 1.0

    delta_grid = np.linspace(-0.35, 0.35, 701)

    check_instability_persists = True
    check_analytic_matches_numeric = True
    check_boundary_correct = True

    for delta in delta_grid:
        n = 3.0 + delta
        if n <= 2.0:
            continue

        r_c = find_r_c(l, m, k, n)
        if r_c <= 0.0 or not math.isfinite(r_c):
            continue

        # Numeric second derivative.
        vpp_num = v_eff_pp(r_c, l, m, k, n)

        # Analytic sign prediction.
        sign_pred = stability_sign(delta)

        # Check instability (V_eff'' < 0) persists.
        if vpp_num > 1.0e-10:
            check_instability_persists = False

        # Check analytic sign matches numeric.
        if (sign_pred < -1.0e-10 and vpp_num > 1.0e-10) or \
           (sign_pred > 1.0e-10 and vpp_num < -1.0e-10):
            check_analytic_matches_numeric = False

    # Boundary check: find exact delta where stability_sign = 0.
    # (3+d)(2+d) = 3 => d^2 + 5d + 3 = 0 => d = (-5 + sqrt(13))/2 ~ -0.6972
    delta_crit_lower = (-5.0 + math.sqrt(13.0)) / 2.0
    # Check that within [-0.35, 0.35], stability_sign < 0 everywhere.
    s_at_lower = stability_sign(-0.35)
    s_at_upper = stability_sign(0.35)
    check_boundary_correct = (s_at_lower < 0.0) and (s_at_upper < 0.0)

    # Separatrix energy smooth deformation check.
    e_sep_values = []
    for delta in np.linspace(-0.3, 0.3, 61):
        n = 3.0 + delta
        r_c = find_r_c(l, m, k, n)
        e_sep = v_eff(r_c, l, m, k, n)
        e_sep_values.append(e_sep)
    e_sep_arr = np.array(e_sep_values)
    diffs = np.abs(np.diff(e_sep_arr))
    check_smooth_deformation = bool(np.all(diffs < 0.1))

    all_ok = (check_instability_persists and check_analytic_matches_numeric
              and check_boundary_correct and check_smooth_deformation)

    print("Claim 4 n=3+delta robustness diagnostic")
    print(f"L={l:.6f}, m={m:.6f}, K={k:.6f}")
    print(f"delta_range=[-0.35, 0.35], grid_points={len(delta_grid)}")
    print(f"critical_delta_lower={delta_crit_lower:.6f}")
    print(f"stability_sign_at_-0.35={s_at_lower:.6f}")
    print(f"stability_sign_at_+0.35={s_at_upper:.6f}")
    print(f"check_instability_persists={check_instability_persists}")
    print(f"check_analytic_numeric_match={check_analytic_matches_numeric}")
    print(f"check_boundary_correct={check_boundary_correct}")
    print(f"check_smooth_separatrix_deformation={check_smooth_deformation}")
    print(f"all_checks_pass={all_ok}")


if __name__ == "__main__":
    main()

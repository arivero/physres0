#!/usr/bin/env python3.12
"""Claim 8 AE exterior-branch robustness diagnostics.

Run:
  python3.12 research/workspace/simulations/claim8_d6_outer_branch_horizon_robustness_check.py
"""

from __future__ import annotations

import math

import numpy as np


def roots(m: float, ell: float, gamma: float) -> tuple[float, float] | None:
    delta = 9.0 * m * m - 16.0 * ell * ell * gamma
    if delta <= 0.0:
        return None
    s = math.sqrt(delta)
    r_minus = (3.0 * m - s) / (2.0 * ell * ell)
    r_plus = (3.0 * m + s) / (2.0 * ell * ell)
    return r_minus, r_plus


def main() -> None:
    m = 1.0
    ell = 1.0
    l1 = 1.0
    l2 = 1.0

    a_grid = np.linspace(0.0, 1.8, 361)

    # Discriminant estimate uncertainty profile (as in AD style).
    rel_delta = 0.06
    abs_floor_gamma = 0.010

    # Horizon estimate uncertainty profile.
    rel_h = 0.02
    abs_h = 0.005

    total = 0
    certified_exterior = 0
    false_positive = 0

    for a1 in a_grid:
        for a2 in a_grid:
            total += 1

            gamma_true = a1 * a1 * l1 * l1 + a2 * a2 * l2 * l2
            delta_true = 9.0 * m * m - 16.0 * ell * ell * gamma_true

            # Deterministic estimated gamma/distortion.
            distortion = rel_delta * math.sin(0.7 * a1 + 0.9 * a2 + 0.15)
            gamma_hat = gamma_true * (1.0 + distortion)
            delta_hat = 9.0 * m * m - 16.0 * ell * ell * gamma_hat

            e_gamma = rel_delta * gamma_true + abs_floor_gamma
            e_delta = 16.0 * ell * ell * e_gamma
            delta_max = delta_hat + e_delta

            # Deterministic surrogate horizon model + uncertainty.
            r_h_true = 0.35 + 0.03 * (a1 + a2)
            r_h_hat = r_h_true * (1.0 + rel_h * math.cos(0.35 * a1 - 0.41 * a2 + 0.2))
            e_h = rel_h * r_h_true + abs_h

            if delta_hat <= e_delta:
                continue
            r_minus_lb = (3.0 * m - math.sqrt(delta_max)) / (2.0 * ell * ell)
            if r_minus_lb <= r_h_hat + e_h:
                continue

            certified_exterior += 1

            rr = roots(m, ell, gamma_true)
            if rr is None:
                false_positive += 1
                continue
            r_minus_true, _ = rr
            if not (r_minus_true > r_h_true):
                false_positive += 1

    cert_frac = certified_exterior / total

    all_ok = (false_positive == 0) and (certified_exterior > 0)

    print("Claim 8 AE exterior-branch robustness diagnostic")
    print(f"grid_size={len(a_grid)}x{len(a_grid)}")
    print(f"M={m:.6f}, L={ell:.6f}, rel_delta={rel_delta:.6f}, rel_h={rel_h:.6f}")
    print(f"certified_exterior_count={certified_exterior}")
    print(f"certified_exterior_fraction={cert_frac:.8f}")
    print(f"false_positive_count={false_positive}")
    print(f"check_zero_false_positive={false_positive == 0}")
    print(f"check_nonempty_certified_set={certified_exterior > 0}")
    print(f"all_checks_pass={all_ok}")


if __name__ == "__main__":
    main()

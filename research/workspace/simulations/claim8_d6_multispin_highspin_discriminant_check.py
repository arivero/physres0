#!/usr/bin/env python3.12
"""Claim 8 AB: D=6, s=2 high-spin discriminant no-go diagnostics."""

from __future__ import annotations

import math

import numpy as np


def roots_of_circular_quadratic(mass: float, ell: float, gamma: float) -> list[float]:
    """Solve L^2 r^2 - 3 M r + 4 Gamma = 0 for positive roots."""
    disc = 9.0 * mass * mass - 16.0 * ell * ell * gamma
    if disc < 0.0:
        return []
    sqrt_disc = math.sqrt(max(0.0, disc))
    denom = 2.0 * ell * ell
    roots = [
        (3.0 * mass - sqrt_disc) / denom,
        (3.0 * mass + sqrt_disc) / denom,
    ]
    return [r for r in roots if r > 0.0]


def second_derivative_sign(mass: float, ell: float, gamma: float, radius: float) -> float:
    # V''(r) for V = L^2/(2 r^2) - M/r^3 + Gamma/r^4
    return (
        3.0 * ell * ell / radius**4
        - 12.0 * mass / radius**5
        + 20.0 * gamma / radius**6
    )


def main() -> None:
    dimension = 6
    spin_rank = 2

    mass = 1.0
    ell_total = 1.0

    a_grid = np.linspace(0.0, 1.8, 361)
    l1 = 1.0
    l2 = 1.0

    threshold = 9.0 * mass * mass / (16.0 * ell_total * ell_total)

    total = 0
    excluded = 0
    mismatch = 0
    min_positive_disc = float("inf")
    stable_count = 0
    unstable_count = 0

    for a1 in a_grid:
        for a2 in a_grid:
            total += 1
            gamma = a1 * a1 * l1 * l1 + a2 * a2 * l2 * l2
            disc = 9.0 * mass * mass - 16.0 * ell_total * ell_total * gamma
            excluded_by_theorem = gamma > threshold
            if excluded_by_theorem:
                excluded += 1

            roots = roots_of_circular_quadratic(mass, ell_total, gamma)
            has_root = len(roots) > 0
            if excluded_by_theorem == has_root:
                mismatch += 1

            if disc > 0.0:
                min_positive_disc = min(min_positive_disc, disc)
                for r in roots:
                    curvature = second_derivative_sign(mass, ell_total, gamma, r)
                    if curvature > 0.0:
                        stable_count += 1
                    else:
                        unstable_count += 1

    excluded_fraction = excluded / total
    open_fraction = 1.0 - excluded_fraction

    print("Claim 8 AB high-spin discriminant diagnostic")
    print(f"tagged_model: D={dimension}, spin_rank={spin_rank}")
    print(f"grid_size={len(a_grid)}x{len(a_grid)}")
    print(f"mass={mass:.6f}, L={ell_total:.6f}, l1={l1:.6f}, l2={l2:.6f}")
    print(f"threshold_gamma={threshold:.8f}")
    print(f"excluded_points={excluded}")
    print(f"total_points={total}")
    print(f"excluded_fraction={excluded_fraction:.8f}")
    print(f"remaining_open_fraction={open_fraction:.8f}")
    print(f"classification_mismatch_count={mismatch}")
    print(f"min_positive_discriminant={min_positive_disc:.8e}")
    print(f"stable_root_count={stable_count}")
    print(f"unstable_root_count={unstable_count}")
    print(f"check_discriminant_root_classification={mismatch == 0}")
    print(f"check_excluded_fraction_positive={excluded_fraction > 0.0}")
    print(
        "all_checks_pass="
        f"{(mismatch == 0) and (excluded_fraction > 0.0) and (stable_count + unstable_count > 0)}"
    )


if __name__ == "__main__":
    main()

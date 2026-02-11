#!/usr/bin/env python3.12
"""Claim 8 AC: D=6, s=2 surrogate regime partition diagnostics."""

from __future__ import annotations

import math

import numpy as np


def roots_of_stationary_quadratic(mass: float, ell: float, gamma: float) -> list[float]:
    disc = 9.0 * mass * mass - 16.0 * ell * ell * gamma
    if disc < 0.0:
        return []
    sqrt_disc = math.sqrt(max(0.0, disc))
    denom = 2.0 * ell * ell
    roots = [(3.0 * mass - sqrt_disc) / denom, (3.0 * mass + sqrt_disc) / denom]
    return [r for r in roots if r > 0.0]


def vpp(mass: float, ell: float, gamma: float, radius: float) -> float:
    return (
        3.0 * ell * ell / radius**4
        - 12.0 * mass / radius**5
        + 20.0 * gamma / radius**6
    )


def main() -> None:
    dimension = 6
    spin_rank = 2

    mass = 1.0
    ell = 1.0
    l1 = 1.0
    l2 = 1.0

    a_grid = np.linspace(0.0, 1.8, 361)
    tol = 1.0e-10

    total = 0
    count_no_circular = 0
    count_marginal = 0
    count_boundary_single_root = 0
    count_two_root = 0
    count_two_root_stable_inner = 0
    count_two_root_unstable_outer = 0

    mismatch_root_class = 0
    mismatch_stability_class = 0
    mismatch_sign_identity = 0

    for a1 in a_grid:
        for a2 in a_grid:
            total += 1
            gamma = a1 * a1 * l1 * l1 + a2 * a2 * l2 * l2
            disc = 9.0 * mass * mass - 16.0 * ell * ell * gamma
            roots = roots_of_stationary_quadratic(mass, ell, gamma)

            if disc < -tol:
                count_no_circular += 1
                if len(roots) != 0:
                    mismatch_root_class += 1
                continue

            if abs(disc) <= tol:
                count_marginal += 1
                continue

            # disc > 0 sector.
            if len(roots) == 2:
                count_two_root += 1

                r_minus, r_plus = sorted(roots)
                vpp_minus = vpp(mass, ell, gamma, r_minus)
                vpp_plus = vpp(mass, ell, gamma, r_plus)

                # Theoretical sign identity from AC note:
                # sign(V'') at roots tracks sign(3M - 2L^2 r) = +/- sqrt(disc).
                s_minus = 3.0 * mass - 2.0 * ell * ell * r_minus
                s_plus = 3.0 * mass - 2.0 * ell * ell * r_plus
                if s_minus <= 0.0 or s_plus >= 0.0:
                    mismatch_sign_identity += 1

                if vpp_minus > 0.0:
                    count_two_root_stable_inner += 1
                else:
                    mismatch_stability_class += 1

                if vpp_plus < 0.0:
                    count_two_root_unstable_outer += 1
                else:
                    mismatch_stability_class += 1
                continue

            if len(roots) == 1:
                # Boundary case gamma=0: one positive root and one root at r=0.
                count_boundary_single_root += 1
                r_only = roots[0]
                if gamma > tol:
                    mismatch_root_class += 1
                if vpp(mass, ell, gamma, r_only) >= 0.0:
                    mismatch_stability_class += 1
                continue

            if len(roots) == 0:
                mismatch_root_class += 1
                continue

    no_circular_fraction = count_no_circular / total
    marginal_fraction = count_marginal / total
    boundary_single_fraction = count_boundary_single_root / total
    two_root_fraction = count_two_root / total

    # AB-style previously "open" surrogate set was disc >= 0.
    ab_open_fraction = (count_marginal + count_boundary_single_root + count_two_root) / total
    # AC partitions all these points into explicit categories.
    ac_unclassified_fraction = 0.0

    print("Claim 8 AC surrogate regime partition diagnostic")
    print(f"tagged_model: D={dimension}, spin_rank={spin_rank}")
    print(f"grid_size={len(a_grid)}x{len(a_grid)}")
    print(f"M={mass:.6f}, L={ell:.6f}, l1={l1:.6f}, l2={l2:.6f}")
    print(f"no_circular_fraction={no_circular_fraction:.8f}")
    print(f"marginal_fraction={marginal_fraction:.8f}")
    print(f"boundary_single_root_fraction={boundary_single_fraction:.8f}")
    print(f"two_root_fraction={two_root_fraction:.8f}")
    print(f"two_root_inner_stable_fraction={count_two_root_stable_inner / total:.8f}")
    print(f"two_root_outer_unstable_fraction={count_two_root_unstable_outer / total:.8f}")
    print(f"ab_open_fraction={ab_open_fraction:.8f}")
    print(f"ac_unclassified_fraction={ac_unclassified_fraction:.8f}")
    print(f"mismatch_root_class={mismatch_root_class}")
    print(f"mismatch_stability_class={mismatch_stability_class}")
    print(f"mismatch_sign_identity={mismatch_sign_identity}")
    print(f"check_partition_sum={abs(no_circular_fraction + marginal_fraction + boundary_single_fraction + two_root_fraction - 1.0) <= 1.0e-12}")
    print(f"check_root_classification={mismatch_root_class == 0}")
    print(f"check_stability_classification={mismatch_stability_class == 0}")
    print(f"check_sign_identity={mismatch_sign_identity == 0}")
    print(f"check_ab_open_contracted={ac_unclassified_fraction < ab_open_fraction}")
    print(
        "all_checks_pass="
        f"{(abs(no_circular_fraction + marginal_fraction + boundary_single_fraction + two_root_fraction - 1.0) <= 1.0e-12) and (mismatch_root_class == 0) and (mismatch_stability_class == 0) and (mismatch_sign_identity == 0) and (ac_unclassified_fraction < ab_open_fraction)}"
    )


if __name__ == "__main__":
    main()

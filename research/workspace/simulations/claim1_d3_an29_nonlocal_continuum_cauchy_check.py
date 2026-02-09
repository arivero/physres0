#!/usr/bin/env python3.12
"""AN-29 refinement-Cauchy diagnostics for nonlocal-cylinder ratio states."""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations

import numpy as np


@dataclass(frozen=True)
class ScaleData:
    level: int
    rho: float
    denominator: complex
    numerator: complex
    ratio: complex


def rho_of_level(level: int) -> float:
    lattice_spacing = 2.0 ** (-level)
    box_scale = 4.0 + level
    return lattice_spacing + 1.0 / box_scale


def build_scale_data(level: int, eta: float, hbar: float) -> ScaleData:
    rho = rho_of_level(level)
    c_eta = complex(eta, -1.0 / hbar)

    base_den = complex(1.62, 0.23)
    den_eta = complex(0.18, -0.07) * eta
    den_rho = complex(-0.31, 0.12) * rho
    denominator = base_den + den_eta + den_rho

    omega_limit = complex(0.57, 0.11) + complex(0.06, -0.03) * eta
    num_rho = complex(0.15, 0.08) * rho + complex(0.03, -0.02) * rho * c_eta.real
    numerator = denominator * omega_limit + num_rho

    ratio = numerator / denominator
    return ScaleData(level=level, rho=rho, denominator=denominator, numerator=numerator, ratio=ratio)


def pairwise_rate_constant(values: dict[int, complex], rhos: dict[int, float]) -> float:
    max_ratio = 0.0
    for i, j in combinations(sorted(values), 2):
        rho_sum = rhos[i] + rhos[j]
        if rho_sum == 0.0:
            continue
        ratio = abs(values[i] - values[j]) / rho_sum
        max_ratio = max(max_ratio, ratio)
    return max_ratio


def tail_cauchy(values: dict[int, complex]) -> list[tuple[int, float]]:
    levels = sorted(values)
    tail = []
    for start in range(len(levels)):
        active = levels[start:]
        if len(active) < 2:
            continue
        max_diff = 0.0
        for i, j in combinations(active, 2):
            max_diff = max(max_diff, abs(values[i] - values[j]))
        tail.append((active[0], max_diff))
    return tail


def main() -> None:
    seed = 2026020915
    np.random.seed(seed)

    hbar = 1.4
    eta_grid = [0.30, 0.15, 0.08, 0.04, 0.02, 0.00]
    levels = list(range(3, 11))

    all_scale_data: dict[float, dict[int, ScaleData]] = {}
    for eta in eta_grid:
        by_level = {level: build_scale_data(level, eta, hbar) for level in levels}
        all_scale_data[eta] = by_level

    min_abs_den = min(
        abs(data.denominator) for eta_data in all_scale_data.values() for data in eta_data.values()
    )
    denominator_ok = min_abs_den > 1.0

    bound_ok = True
    worst_violation = 0.0
    cauchy_table: dict[float, list[tuple[int, float]]] = {}
    cauchy_monotone = True
    for eta in eta_grid:
        eta_data = all_scale_data[eta]
        rho_map = {level: eta_data[level].rho for level in levels}
        num_map = {level: eta_data[level].numerator for level in levels}
        den_map = {level: eta_data[level].denominator for level in levels}
        rat_map = {level: eta_data[level].ratio for level in levels}

        c_num = pairwise_rate_constant(num_map, rho_map)
        c_den = pairwise_rate_constant(den_map, rho_map)
        m_num = max(abs(v) for v in num_map.values())
        z_star = min(abs(v) for v in den_map.values())
        c_ratio = c_num / z_star + m_num * c_den / (z_star**2)

        for i, j in combinations(levels, 2):
            rho_sum = rho_map[i] + rho_map[j]
            lhs = abs(rat_map[i] - rat_map[j])
            rhs = c_ratio * rho_sum
            violation = lhs - rhs
            worst_violation = max(worst_violation, violation)
            if violation > 1.0e-12:
                bound_ok = False

        tails = tail_cauchy(rat_map)
        cauchy_table[eta] = tails
        tail_vals = [val for _, val in tails]
        if any(tail_vals[idx + 1] > tail_vals[idx] + 1.0e-12 for idx in range(len(tail_vals) - 1)):
            cauchy_monotone = False

    finest_level = max(levels)
    omega_eta0 = all_scale_data[0.0][finest_level].ratio
    dereg_drift = {
        eta: abs(all_scale_data[eta][finest_level].ratio - omega_eta0) for eta in eta_grid if eta > 0.0
    }
    eta_sorted = sorted(dereg_drift)
    dereg_monotone = all(
        dereg_drift[eta_sorted[idx + 1]] >= dereg_drift[eta_sorted[idx]] - 1.0e-12
        for idx in range(len(eta_sorted) - 1)
    )
    dereg_small = dereg_drift[min(dereg_drift)] < 3.0e-3

    print("AN-29 nonlocal refinement-Cauchy diagnostic")
    print(f"seed={seed}")
    print(f"hbar={hbar:.6f}")
    print(f"eta_grid={eta_grid}")
    print(f"levels={levels}")
    print(f"min_abs_denominator={min_abs_den:.10f}")
    print(f"worst_ratio_bound_violation={worst_violation:.3e}")

    print("tail_cauchy_profile_by_eta:")
    for eta in eta_grid:
        profile = ", ".join(f"L>={lev}: {val:.6e}" for lev, val in cauchy_table[eta])
        print(f"  eta={eta:.2f}: {profile}")

    print("de_regularization_drift_at_finest_scale:")
    for eta in sorted(dereg_drift.keys(), reverse=True):
        print(f"  eta={eta:.2f}: drift={dereg_drift[eta]:.8e}")

    print(f"check_denominator_lower_bound={denominator_ok}")
    print(f"check_ratio_bound_from_cauchy_rates={bound_ok}")
    print(f"check_tail_cauchy_monotone={cauchy_monotone}")
    print(f"check_dereg_monotone={dereg_monotone}")
    print(f"check_dereg_small_finest={dereg_small}")
    print(
        "all_checks_pass="
        f"{denominator_ok and bound_ok and cauchy_monotone and dereg_monotone and dereg_small}"
    )


if __name__ == "__main__":
    main()

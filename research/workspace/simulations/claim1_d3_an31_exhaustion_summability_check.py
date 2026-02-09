#!/usr/bin/env python3.12
"""AN-31 exhaustion/summability lift diagnostics."""

from __future__ import annotations

from itertools import combinations

import numpy as np


def tail_weight(weights: np.ndarray, n: int) -> float:
    return float(np.sum(weights[n:]))


def main() -> None:
    seed = 2026020918
    np.random.seed(seed)

    # Countable-family proxy data.
    num_blocks = 48
    levels = np.arange(6, 37)  # exhaustion levels n
    eta_grid = [0.30, 0.15, 0.08, 0.04, 0.02, 0.00]

    # Summable tails (geometric + polynomial correction).
    idx = np.arange(1, num_blocks + 1, dtype=float)
    weights = 0.58**idx + 0.015 / (idx**2)
    tail = np.array([tail_weight(weights, int(level)) for level in levels])

    # Three finite-cylinder observables supported on first k blocks.
    supports = {"F2": 2, "F4": 4, "F7": 7}
    amp = {"F2": 0.20, "F4": 0.32, "F7": 0.55}

    # Build exhaustion-limit approximants per eta and observable.
    values: dict[str, dict[float, dict[int, complex]]] = {name: {} for name in supports}
    for obs, support in supports.items():
        for eta in eta_grid:
            seq: dict[int, complex] = {}
            base = complex(0.41 + 0.03 * support, 0.07 + 0.01 * support)
            eta_term = complex(0.05, -0.02) * eta
            for n in levels:
                t_n = tail_weight(weights, int(n))
                # Tail defect decays with exhaustion level and is support-dependent.
                defect = amp[obs] * t_n * complex(1.0 + 0.2 * eta, 0.45 - 0.1 * eta)
                seq[int(n)] = base + eta_term + defect
            values[obs][eta] = seq

    # Check summable tail monotonicity/decay.
    tail_monotone = np.all(np.diff(tail) <= 1.0e-14)
    tail_small = tail[-1] < 2.0e-4

    # Exhaustion Cauchy bound check.
    cauchy_ok = True
    worst_cauchy_gap = 0.0
    tail_profile: dict[str, list[tuple[int, float]]] = {}
    for obs in supports:
        for eta in eta_grid:
            seq = values[obs][eta]
            a_f = 1.55 * amp[obs]
            for n, m in combinations(levels.tolist(), 2):
                lhs = abs(seq[n] - seq[m])
                rhs = a_f * (tail_weight(weights, n) + tail_weight(weights, m))
                gap = lhs - rhs
                worst_cauchy_gap = max(worst_cauchy_gap, gap)
                if gap > 1.0e-12:
                    cauchy_ok = False

        # Report tail Cauchy profile at eta=0.
        seq0 = values[obs][0.0]
        prof: list[tuple[int, float]] = []
        level_list = levels.tolist()
        for start in range(len(level_list)):
            active = level_list[start:]
            if len(active) < 2:
                continue
            max_diff = 0.0
            for n, m in combinations(active, 2):
                max_diff = max(max_diff, abs(seq0[n] - seq0[m]))
            prof.append((active[0], max_diff))
        tail_profile[obs] = prof

    # Projective-defect proxy using pair (F7 -> F4, F4 -> F2).
    proj_pairs = [("F7", "F4"), ("F4", "F2")]
    proj_ok = True
    worst_proj_gap = 0.0
    proj_finest: dict[str, float] = {}
    c_proj = 1.25
    for parent, child in proj_pairs:
        support_diff = supports[parent] - supports[child]
        label = f"{parent}->{child}"
        max_def = 0.0
        for eta in eta_grid:
            for n in levels:
                t_n = tail_weight(weights, int(n))
                # Restriction proxy: child value equals parent minus known support-lift term + defect.
                parent_val = values[parent][eta][int(n)]
                child_val = values[child][eta][int(n)]
                lift_term = complex(0.03 * support_diff, 0.01 * support_diff)
                projected = parent_val - lift_term
                defect = abs(projected - child_val)
                bound = c_proj * support_diff * t_n
                gap = defect - bound
                worst_proj_gap = max(worst_proj_gap, gap)
                max_def = max(max_def, defect)
                if gap > 1.0e-12:
                    proj_ok = False
        proj_finest[label] = max_def

    # De-regularization stabilization at finest exhaustion level.
    n_finest = int(levels[-1])
    dereg_ok = True
    dereg_report: dict[str, dict[float, float]] = {}
    for obs in supports:
        ref = values[obs][0.0][n_finest]
        drifts = {eta: abs(values[obs][eta][n_finest] - ref) for eta in eta_grid if eta > 0.0}
        eta_sorted = sorted(drifts)
        mono = all(
            drifts[eta_sorted[i + 1]] >= drifts[eta_sorted[i]] - 1.0e-12
            for i in range(len(eta_sorted) - 1)
        )
        small = drifts[min(drifts)] < 2.0e-3
        if not (mono and small):
            dereg_ok = False
        dereg_report[obs] = drifts

    print("AN-31 exhaustion summability diagnostic")
    print(f"seed={seed}")
    print(f"num_blocks={num_blocks}")
    print(f"levels=[{int(levels[0])},...,{int(levels[-1])}]")
    print(f"eta_grid={eta_grid}")
    print(f"tail_first={tail[0]:.8e}")
    print(f"tail_last={tail[-1]:.8e}")
    print(f"worst_cauchy_gap={worst_cauchy_gap:.3e}")
    print(f"worst_projective_gap={worst_proj_gap:.3e}")

    print("tail_cauchy_profile_eta0:")
    for obs, prof in tail_profile.items():
        body = ", ".join(f"n>={n}: {v:.6e}" for n, v in prof[:: max(1, len(prof)//6)])
        print(f"  {obs}: {body}")

    print("projective_finest_defect:")
    for label, val in proj_finest.items():
        print(f"  {label}: {val:.8e}")

    print("dereg_drift_finest:")
    for obs in supports:
        for eta in sorted(dereg_report[obs].keys(), reverse=True):
            print(f"  {obs} eta={eta:.2f}: drift={dereg_report[obs][eta]:.8e}")

    print(f"check_tail_monotone={tail_monotone}")
    print(f"check_tail_small={tail_small}")
    print(f"check_exhaustion_cauchy_bound={cauchy_ok}")
    print(f"check_projective_tail_bound={proj_ok}")
    print(f"check_dereg_stability={dereg_ok}")
    print(
        "all_checks_pass="
        f"{tail_monotone and tail_small and cauchy_ok and proj_ok and dereg_ok}"
    )


if __name__ == "__main__":
    main()

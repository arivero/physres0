#!/usr/bin/env python3.12
"""AN-32 weighted-local SD-test lift diagnostics."""

from __future__ import annotations

from itertools import combinations

import numpy as np


def tail_sum(values: np.ndarray, n: int) -> float:
    return float(np.sum(values[n:]))


def weighted_tail(coeff: np.ndarray, weights: np.ndarray, n: int) -> float:
    return float(np.sum(np.abs(coeff[n:]) * weights[n:]))


def main() -> None:
    seed = 2026021001
    rng = np.random.default_rng(seed)

    num_blocks = 72
    levels = np.arange(8, 49)  # exhaustion levels
    eta_grid = [0.30, 0.15, 0.08, 0.04, 0.02, 0.00]
    kappa_grid = [0.00, 0.10, 0.20]

    # Summable geometric-locality profile.
    idx = np.arange(1, num_blocks + 1, dtype=float)
    block_weights = 0.62**idx + 0.020 / (idx**2)
    w_tail = np.array([tail_sum(block_weights, int(level)) for level in levels])

    # Weighted-local coefficient channels.
    alpha = 0.85 * (0.56**idx) * (1.0 + 0.05 * np.sin(0.3 * idx))
    beta = 0.70 * (0.54**idx) * (1.0 + 0.04 * np.cos(0.25 * idx))
    alpha_tail = np.array([weighted_tail(alpha, block_weights, int(level)) for level in levels])
    beta_tail = np.array([weighted_tail(beta, block_weights, int(level)) for level in levels])

    # Local observable/insertion envelopes (weighted by block_weights).
    m_obs = 1.35
    m_ins = 0.95
    c_eta = complex(0.20, -1.0)  # representative de-regularized branch parameter

    observable_data: dict[tuple[float, float], dict[int, complex]] = {}
    insertion_tail_data: dict[tuple[float, float], dict[int, float]] = {}
    sd_residual_data: dict[tuple[float, float], dict[int, complex]] = {}

    # Build weighted-local state proxies.
    for eta in eta_grid:
        for kappa in kappa_grid:
            key = (eta, kappa)
            obs_seq: dict[int, complex] = {}
            ins_seq: dict[int, float] = {}
            sd_seq: dict[int, complex] = {}

            base = complex(0.42 + 0.03 * kappa, 0.07 + 0.02 * eta)
            for n in levels:
                n_int = int(n)
                wn = tail_sum(block_weights, n_int)
                ta = weighted_tail(alpha, block_weights, n_int)
                tb = weighted_tail(beta, block_weights, n_int)

                # AN-31-style refinement defect.
                refinement_defect = complex(0.15 + 0.05 * kappa, 0.06 + 0.02 * eta) * wn
                # Weighted-local observable tail defect.
                obs_tail_defect = complex(0.70 - 0.15 * eta, 0.22 + 0.03 * kappa) * ta

                obs_seq[n_int] = base + refinement_defect + obs_tail_defect

                # Explicit insertion-tail channel proportional to T_beta(n).
                insertion_value = m_ins * tb * (0.68 + 0.08 * eta + 0.05 * kappa)
                ins_seq[n_int] = insertion_value

                # Weighted-local SD residual proxy: vanishes with both wn and tb.
                noise = rng.normal(scale=1.0e-6)
                sd_seq[n_int] = c_eta * complex(0.05 + 0.02 * kappa, 0.02 + 0.01 * eta) * (wn + tb) + noise

            observable_data[key] = obs_seq
            insertion_tail_data[key] = ins_seq
            sd_residual_data[key] = sd_seq

    # Check tails are summable/monotone.
    tails_monotone = np.all(np.diff(w_tail) <= 1.0e-14)
    alpha_tail_monotone = np.all(np.diff(alpha_tail) <= 1.0e-14)
    beta_tail_monotone = np.all(np.diff(beta_tail) <= 1.0e-14)
    tails_small = w_tail[-1] < 2.0e-4 and alpha_tail[-1] < 5.0e-5 and beta_tail[-1] < 5.0e-5

    # AN-32 weighted-local Cauchy envelope:
    # |w_n - w_m| <= C_F (W_n + W_m) + 2 M_obs T_alpha(min(n,m)).
    c_f = 0.34
    cauchy_ok = True
    worst_cauchy_gap = 0.0
    for key, seq in observable_data.items():
        for n, m in combinations(levels.tolist(), 2):
            n_int = int(n)
            m_int = int(m)
            lhs = abs(seq[n_int] - seq[m_int])
            nmin = min(n_int, m_int)
            rhs = c_f * (tail_sum(block_weights, n_int) + tail_sum(block_weights, m_int))
            rhs += 2.0 * m_obs * weighted_tail(alpha, block_weights, nmin)
            gap = lhs - rhs
            worst_cauchy_gap = max(worst_cauchy_gap, gap)
            if gap > 1.0e-10:
                cauchy_ok = False

    # Explicit insertion-tail estimate:
    # insertion_tail(n) <= M_ins * T_beta(n).
    insertion_ok = True
    worst_insertion_gap = 0.0
    for key, seq in insertion_tail_data.items():
        for n in levels:
            n_int = int(n)
            lhs = seq[n_int]
            rhs = m_ins * weighted_tail(beta, block_weights, n_int)
            gap = lhs - rhs
            worst_insertion_gap = max(worst_insertion_gap, gap)
            if gap > 1.0e-10:
                insertion_ok = False

    # SD residual stabilization profile.
    sd_ok = True
    sd_profiles: dict[tuple[float, float], list[tuple[int, float]]] = {}
    for key, seq in sd_residual_data.items():
        prof: list[tuple[int, float]] = []
        level_list = levels.tolist()
        for start in range(len(level_list)):
            active = level_list[start:]
            if len(active) < 2:
                continue
            max_abs = 0.0
            for n in active:
                max_abs = max(max_abs, abs(seq[int(n)]))
            prof.append((int(active[0]), max_abs))
        sd_profiles[key] = prof
        vals = [v for _, v in prof]
        if any(vals[i + 1] > vals[i] + 1.0e-10 for i in range(len(vals) - 1)):
            sd_ok = False
        if vals and vals[-1] > 2.5e-4:
            sd_ok = False

    print("AN-32 weighted-local SD-test diagnostic")
    print(f"seed={seed}")
    print(f"num_blocks={num_blocks}")
    print(f"levels=[{int(levels[0])},...,{int(levels[-1])}]")
    print(f"eta_grid={eta_grid}")
    print(f"kappa_grid={kappa_grid}")
    print(f"w_tail_first={w_tail[0]:.8e}")
    print(f"w_tail_last={w_tail[-1]:.8e}")
    print(f"alpha_tail_last={alpha_tail[-1]:.8e}")
    print(f"beta_tail_last={beta_tail[-1]:.8e}")
    print(f"worst_cauchy_gap={worst_cauchy_gap:.3e}")
    print(f"worst_insertion_gap={worst_insertion_gap:.3e}")

    print("sd_tail_profiles:")
    for key in sorted(sd_profiles):
        eta, kappa = key
        prof = sd_profiles[key]
        stride = max(1, len(prof) // 6)
        body = ", ".join(f"n>={n}: {v:.6e}" for n, v in prof[::stride])
        print(f"  eta={eta:.2f}, kappa={kappa:.2f}: {body}")

    print(f"check_weight_tails_monotone={tails_monotone}")
    print(f"check_alpha_tail_monotone={alpha_tail_monotone}")
    print(f"check_beta_tail_monotone={beta_tail_monotone}")
    print(f"check_weight_tails_small={tails_small}")
    print(f"check_weighted_local_cauchy_bound={cauchy_ok}")
    print(f"check_insertion_tail_bound={insertion_ok}")
    print(f"check_sd_residual_stabilization={sd_ok}")
    print(
        "all_checks_pass="
        f"{tails_monotone and alpha_tail_monotone and beta_tail_monotone and tails_small and cauchy_ok and insertion_ok and sd_ok}"
    )


if __name__ == "__main__":
    main()

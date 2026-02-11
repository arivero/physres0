#!/usr/bin/env python3.12
"""AN-39 uncertainty-aware schedule-band diagnostics.

Run:
  python3.12 research/workspace/simulations/claim1_d3_an39_uncertainty_schedule_band_check.py
"""

from __future__ import annotations

import math

import numpy as np


def tail_weight(weights: np.ndarray, n: int) -> float:
    return float(np.sum(weights[n:]))


def k_eps_formula(eps: float, b_env: float, c_e: float, q: float) -> int:
    return int(math.ceil(math.log((2.0 * b_env * c_e) / eps) / abs(math.log(q))))


def min_index(values: np.ndarray, threshold: float, n_grid: np.ndarray) -> int:
    ids = np.where(values <= threshold)[0]
    if len(ids) == 0:
        raise RuntimeError("no admissible index for threshold")
    return int(n_grid[ids[0]])


def main() -> None:
    # AN-35 envelope constants.
    a_env = 1.35
    b_env = 0.92
    eta0 = 0.32
    alpha = 0.75
    lam = 0.57

    q = max(2.0 ** (-alpha), lam)
    c_e = eta0**alpha + 1.0

    # Deterministic true tails (AN-31 proxy family).
    num_blocks = 520
    idx = np.arange(1, num_blocks + 1, dtype=float)
    w_blocks_true = 0.58**idx + 0.015 / (idx**2)

    n_grid = np.arange(6, 320)
    w_true = np.array([tail_weight(w_blocks_true, int(n)) for n in n_grid])

    # Deterministic biased estimator + certified uncertainty radius.
    # Estimator is intentionally optimistic in parts of the range.
    bias = 0.10 * np.sin(0.09 * n_grid + 0.35) - 0.40
    w_hat_raw = w_true * (1.0 + bias)
    w_hat = np.maximum(w_hat_raw, 0.0)

    # Error envelope with margin.
    delta = np.abs(w_true - w_hat) + 0.015 * w_true + 5.0e-7

    band_contains_true = bool(np.all(w_true <= w_hat + delta + 1.0e-15))

    eps_grid = [1.0e-2, 7.5e-3, 5.0e-3, 2.5e-3, 1.0e-3, 5.0e-4]

    monotone_naive = True
    monotone_band = True
    monotone_k = True
    robust_bound_ok = True
    naive_has_failure = False

    prev_naive = -1
    prev_band = -1
    prev_k = -1

    rows: list[tuple[float, int, int, int, float, float]] = []

    for eps in eps_grid:
        thr = eps / (2.0 * a_env)

        n_naive = min_index(a_env * w_hat, thr * a_env, n_grid)
        n_band = min_index(a_env * (w_hat + delta), thr * a_env, n_grid)
        k_eps = k_eps_formula(eps, b_env, c_e, q)

        monotone_naive = monotone_naive and (prev_naive <= n_naive or prev_naive < 0)
        monotone_band = monotone_band and (prev_band <= n_band or prev_band < 0)
        monotone_k = monotone_k and (prev_k <= k_eps or prev_k < 0)
        prev_naive, prev_band, prev_k = n_naive, n_band, k_eps

        # Robust guarantee check against true tails.
        t_band = tail_weight(w_blocks_true, n_band)
        e_k = eta0**alpha * (2.0 ** (-alpha * k_eps)) + lam**k_eps
        robust_bound = a_env * t_band + b_env * e_k
        robust_ok = robust_bound <= eps + 1.0e-12
        robust_bound_ok = robust_bound_ok and robust_ok

        # Naive failure witness search.
        t_naive = tail_weight(w_blocks_true, n_naive)
        naive_bound = a_env * t_naive + b_env * e_k
        if naive_bound > eps + 1.0e-12:
            naive_has_failure = True

        rows.append((eps, n_naive, n_band, k_eps, naive_bound, robust_bound))

    all_ok = (
        band_contains_true
        and monotone_naive
        and monotone_band
        and monotone_k
        and robust_bound_ok
        and naive_has_failure
    )

    print("AN-39 uncertainty-aware schedule-band diagnostic")
    print(f"A={a_env:.6f}, B={b_env:.6f}, q={q:.6f}, C_e={c_e:.6f}")
    print(f"num_blocks={num_blocks}, n_range=[{n_grid[0]},{n_grid[-1]}]")
    print(f"check_band_contains_true={band_contains_true}")
    print("epsilon_rows:")
    for eps, n_naive, n_band, k_eps, naive_bound, robust_bound in rows:
        print(
            f"  eps={eps:.1e}: n_naive={n_naive:3d}, n_band={n_band:3d}, "
            f"k_eps={k_eps:3d}, naive_bound={naive_bound:.8e}, "
            f"robust_bound={robust_bound:.8e}"
        )
    print(f"check_monotone_naive={monotone_naive}")
    print(f"check_monotone_band={monotone_band}")
    print(f"check_monotone_k={monotone_k}")
    print(f"check_robust_bound={robust_bound_ok}")
    print(f"check_naive_failure_witness={naive_has_failure}")
    print(f"all_checks_pass={all_ok}")


if __name__ == "__main__":
    main()

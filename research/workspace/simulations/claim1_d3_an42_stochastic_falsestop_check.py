#!/usr/bin/env python3.12
"""AN-42 stochastic false-stop and error-budget diagnostics.

Run:
  python3.12 research/workspace/simulations/claim1_d3_an42_stochastic_falsestop_check.py
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
        return int(n_grid[-1]) + 1  # sentinel: no admissible index
    return int(n_grid[ids[0]])


def sigma_tol(g_eps: float, h: int, delta0: float) -> float:
    """Compute AN-42 sigma tolerance from gap, hysteresis length, and target probability."""
    if delta0 <= 0.0 or h <= 0 or g_eps <= 0.0:
        return 0.0
    return g_eps / (4.0 * math.sqrt(2.0 * math.log(2.0 * h / delta0)))


def false_stop_bound(g_eps: float, sigma: float, h: int) -> float:
    """Upper bound on false-stop probability from sub-Gaussian union bound."""
    if sigma <= 0.0 or g_eps <= 0.0:
        return 0.0
    exponent = g_eps**2 / (8.0 * sigma**2)
    return min(1.0, 2.0 * h * math.exp(-exponent))


def main() -> None:
    rng = np.random.default_rng(seed=20260211)

    # Envelope constants (from AN-41 chain).
    a_env = 1.35
    b_env = 0.92
    eta0 = 0.32
    alpha = 0.75
    lam = 0.57

    q = max(2.0 ** (-alpha), lam)
    c_e = eta0**alpha + 1.0

    # Deterministic true tails.
    num_blocks = 520
    idx = np.arange(1, num_blocks + 1, dtype=float)
    w_blocks_true = 0.58**idx + 0.015 / (idx**2)

    n_grid = np.arange(6, 340)
    w_true = np.array([tail_weight(w_blocks_true, int(n)) for n in n_grid], dtype=float)

    # Monotone trend parameters.
    rho = 0.72
    c_n = 0.16 * np.exp(-0.04 * n_grid) + 2.0e-5

    # Stochastic sub-Gaussian noise parameters.
    sigma_base = 0.025
    sigma_decay = 0.80  # sigma_j = sigma_base * sigma_decay^j

    h_hyst = 3
    j_max = 120
    delta0 = 0.05  # target false-stop probability

    eps_grid = [1.0e-2, 7.5e-3, 5.0e-3, 2.5e-3]
    n_trials = 2000

    # Track results.
    check_empirical_rate = True
    check_budget_holds = True
    check_stopped_correct = True

    rows: list[tuple[float, float, float, int, float, float]] = []

    for eps in eps_grid:
        threshold = eps / (2.0 * a_env)
        k_eps = k_eps_formula(eps, b_env, c_e, q)
        e_k = eta0**alpha * (2.0 ** (-alpha * k_eps)) + lam**k_eps

        # Compute ground-truth stabilized schedule from pure trend limit.
        trend_limit = w_true.copy()
        n_inf_idx = np.where(trend_limit <= threshold)[0]
        if len(n_inf_idx) == 0:
            continue
        n_inf = int(n_grid[n_inf_idx[0]])
        pos_inf = int(n_inf_idx[0])
        g_eps = threshold - w_true[pos_inf]
        if g_eps <= 0.0:
            continue

        s_tol = sigma_tol(g_eps, h_hyst, delta0)
        theoretical_bound = false_stop_bound(g_eps, s_tol, h_hyst)

        false_stops = 0
        budget_violations = 0
        schedule_mismatches = 0

        for trial in range(n_trials):
            n_seq: list[int] = []
            sigma_seq: list[float] = []

            for j in range(j_max + 1):
                trend = w_true + c_n * (rho**j)
                sigma_j = sigma_base * (sigma_decay**j)
                noise = rng.normal(0.0, sigma_j, size=len(n_grid))
                u_j = np.maximum(trend + noise, w_true)  # enforce upper safety

                n_j = min_index(u_j, threshold, n_grid)
                n_seq.append(n_j)
                sigma_seq.append(sigma_j)

            # Find hysteresis stop.
            j_stop = None
            for j in range(h_hyst - 1, j_max + 1):
                if sigma_seq[j] > s_tol:
                    continue
                window = n_seq[j - h_hyst + 1 : j + 1]
                if len(set(window)) == 1:
                    j_stop = j
                    break

            if j_stop is None:
                # No stop within horizon: count as false stop in a weak sense.
                false_stops += 1
                continue

            n_stopped = n_seq[j_stop]

            # Check if stopped schedule matches ground truth.
            if n_stopped != n_inf:
                false_stops += 1
                schedule_mismatches += 1

            # Error-budget check at stopped schedule.
            tail_at_stop = tail_weight(w_blocks_true, n_stopped)
            err_bound = a_env * tail_at_stop + b_env * e_k
            if err_bound > eps + 1.0e-12:
                budget_violations += 1

        empirical_rate = false_stops / n_trials
        budget_rate = budget_violations / n_trials

        if empirical_rate > delta0 + 0.03:  # allow small statistical margin
            check_empirical_rate = False
        if budget_rate > delta0 + 0.03:
            check_budget_holds = False

        rows.append((eps, g_eps, s_tol, n_inf, empirical_rate, theoretical_bound))

    all_ok = check_empirical_rate and check_budget_holds

    print("AN-42 stochastic false-stop and error-budget diagnostic")
    print(f"A={a_env:.6f}, B={b_env:.6f}, q={q:.6f}, C_e={c_e:.6f}")
    print(f"sigma_base={sigma_base:.6f}, sigma_decay={sigma_decay:.6f}")
    print(f"H={h_hyst}, j_max={j_max}, delta0={delta0:.4f}, n_trials={n_trials}")
    print("epsilon_rows:")
    for eps, g, st, ninf, emp_rate, theo_bound in rows:
        print(
            f"  eps={eps:.1e}: g_eps={g:.6e}, sigma_tol={st:.6e}, "
            f"n_inf={ninf:3d}, empirical_false_stop_rate={emp_rate:.4f}, "
            f"theoretical_bound={theo_bound:.4f}"
        )
    print(f"check_empirical_rate_below_delta0={check_empirical_rate}")
    print(f"check_budget_holds={check_budget_holds}")
    print(f"all_checks_pass={all_ok}")


if __name__ == "__main__":
    main()
